/****************************************************************************

		THIS SOFTWARE IS NOT COPYRIGHTED  
   
   HP offers the following for use in the public domain.  HP makes no
   warranty with regard to the software or it's performance and the 
   user accepts the software "AS IS" with all faults.

   HP DISCLAIMS ANY WARRANTIES, EXPRESS OR IMPLIED, WITH REGARD
   TO THIS SOFTWARE INCLUDING BUT NOT LIMITED TO THE WARRANTIES
   OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE.

****************************************************************************/

/****************************************************************************
 *  Header: remcom.c,v 1.34 91/03/09 12:29:49 glenne Exp $                   
 *
 *  Module name: remcom.c $  
 *  Revision: 1.34 $
 *  Date: 91/03/09 12:29:49 $
 *  Contributor:     Lake Stevens Instrument Division$
 *  
 *  Description:     low level support for gdb debugger. $
 *
 *  Considerations:  only works on target hardware $
 *
 *  Written by:      Glenn Engel $
 *  ModuleState:     Experimental $ 
 *
 *  NOTES:           See Below $
 * 
 *  To enable debugger support, two things need to happen.  One, a
 *  call to set_debug_traps() is necessary in order to allow any breakpoints
 *  or error conditions to be properly intercepted and reported to gdb.
 *  Two, a breakpoint needs to be generated to begin communication.  This
 *  is most easily accomplished by a call to breakpoint().  Breakpoint()
 *  simulates a breakpoint by executing a trap #1.  The breakpoint instruction
 *  is hardwired to trap #1 because not to do so is a compatibility problem--
 *  there either should be a standard breakpoint instruction, or the protocol
 *  should be extended to provide some means to communicate which breakpoint
 *  instruction is in use (or have the stub insert the breakpoint).
 *  
 *  Some explanation is probably necessary to explain how exceptions are
 *  handled.  When an exception is encountered the 68000 pushes the current
 *  program counter and status register onto the supervisor stack and then
 *  transfers execution to a location specified in it's vector table.
 *  The handlers for the exception vectors are hardwired to jmp to an address
 *  given by the relation:  (exception - 256) * 6.  These are decending 
 *  addresses starting from -6, -12, -18, ...  By allowing 6 bytes for
 *  each entry, a jsr, jmp, bsr, ... can be used to enter the exception 
 *  handler.  Using a jsr to handle an exception has an added benefit of
 *  allowing a single handler to service several exceptions and use the
 *  return address as the key differentiation.  The vector number can be
 *  computed from the return address by [ exception = (addr + 1530) / 6 ].
 *  The sole purpose of the routine _catchException is to compute the
 *  exception number and push it on the stack in place of the return address.
 *  The external function exceptionHandler() is
 *  used to attach a specific handler to a specific m68k exception.
 *  For 68020 machines, the ability to have a return address around just
 *  so the vector can be determined is not necessary because the '020 pushes an
 *  extra word onto the stack containing the vector offset
 * 
 *  Because gdb will sometimes write to the stack area to execute function
 *  calls, this program cannot rely on using the supervisor stack so it
 *  uses it's own stack area reserved in the int array remcomStack.  
 * 
 *************
 *
 *    The following gdb commands are supported:
 * 
 * command          function                               Return value
 * 
 *    g             return the value of the CPU registers  hex data or ENN
 *    G             set the value of the CPU registers     OK or ENN
 * 
 *    mAA..AA,LLLL  Read LLLL bytes at address AA..AA      hex data or ENN
 *    MAA..AA,LLLL: Write LLLL bytes at address AA.AA      OK or ENN
 * 
 *    c             Resume at current address              SNN   ( signal NN)
 *    cAA..AA       Continue at address AA..AA             SNN
 * 
 *    s             Step one instruction                   SNN
 *    sAA..AA       Step one instruction from AA..AA       SNN
 * 
 *    k             kill
 *
 *    ?             What was the last sigval ?             SNN   (signal NN)
 * 
 * All commands and responses are sent with a packet which includes a 
 * checksum.  A packet consists of 
 * 
 * $<packet info>#<checksum>.
 * 
 * where
 * <packet info> :: <characters representing the command or response>
 * <checksum>    :: < two hex digits computed as modulo 256 sum of <packetinfo>>
 * 
 * When a packet is received, it is first acknowledged with either '+' or '-'.
 * '+' indicates a successful transfer.  '-' indicates a failed transfer.
 * 
 * Example:
 * 
 * Host:                  Reply:
 * $m0,10#2a               +$00010203040506070809101112131415#42
 * 
 ****************************************************************************/

#define __RTEMS_VIOLATE_KERNEL_VISIBILITY__
#include <rtems.h>
#include <rtems/error.h>
#include <rtems/bspIo.h>

#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>

#include <stdio.h>
#include <string.h>
#include <setjmp.h>
#include <errno.h>
#include <stdlib.h>
#include <assert.h>

#define HAVE_CEXP

#ifdef HAVE_CEXP
#include <cexp.h>
/* we do no locking - hope nobody messes with the
 * module list during a debugging session
 */
#include <cexpmodP.h>
#endif


#ifdef __PPC__
#include "rtems-gdb-stub-ppc-shared.h"
#else
#error need target specific helper implementation
#endif

#define TID_ANY ((rtems_id)0)
#define TID_ALL ((rtems_id)-1)

/************************************************************************
 *
 * external low-level support routines 
 */

static   FILE *rtems_gdb_strm = 0;

/* write a single character      */
static inline void putDebugChar(int ch)
{
	fputc(ch, rtems_gdb_strm);
}
/* read and return a single char */
static inline int getDebugChar()
{
	return fgetc(rtems_gdb_strm);
}

static inline void flushDebugChars()
{
	fflush(rtems_gdb_strm);
}


/************************/
/* FORWARD DECLARATIONS */
/************************/

static int
pendSomethingHappening(RtemsDebugMsg *, int, char*);

static int resume_stopped_task(rtems_id tid, int sig);

/************************************************************************/
/* BUFMAX defines the maximum number of characters in inbound/outbound buffers*/
/* at least NUMREGBYTES*2 are needed for register packets */
#define BUFMAX 400
#define EXTRABUFSZ	200
#define STATIC 

#define CTRLC  3
#define RTEMS_GDB_Q_LEN 200
#define RTEMS_GDB_PORT 4444

#if (EXTRABUFSZ+15) > NUMREGBYTES
#define CHRBUFSZ (EXTRABUFSZ+15)
#else
#define CHRBUFSZ NUMREGBYTES
#endif


#if BUFMAX < 2*CHRBUFSZ + 100
#  undef  BUFMAX
#  define BUFMAX (2*CHRBUFSZ+100)
#endif

static volatile char initialized=0;  /* boolean flag. != 0 means we've been initialized */

/* Table used by the crc32 function to calcuate the checksum. */
/* CRC32 algorithm from GDB: gdb/remote.c (GPL!!) */
static unsigned long crc32_table[256] =
{0, 0};
                                                                                                                                                         
static unsigned long
crc32 (unsigned char *buf, int len, unsigned int crc)
{
 while (len--)
    {
      crc = (crc << 8) ^ crc32_table[((crc >> 24) ^ *buf) & 255];
      buf++;
    }
  return crc;
}

STATIC rtems_id gdb_pending_id = 0;

int semacount = 0;

static inline void SEMA_INC()
{
	semacount++;
}

static inline void SEMA_DEC()
{
unsigned long flags;
	rtems_interrupt_disable(flags);
	semacount--;
	rtems_interrupt_enable(flags);
}

int     rtems_remote_debug = 4;
/*  debug >  0 prints ill-formed commands in valid packets & checksum errors */ 

static const char hexchars[]="0123456789abcdef";

static rtems_id
thread_helper(char *nm, int pri, int stack, void (*fn)(rtems_task_argument), rtems_task_argument arg);

static RtemsDebugMsg
task_switch_to(RtemsDebugMsg m, rtems_id new_tid);

static int
task_resume(RtemsDebugMsg m, int sig);

static RtemsDebugMsg getFirstMsg(int);

/* list of threads that have stopped */
static CdllNodeRec anchor   = { &anchor, &anchor };

/* list of currently stopped threads */
static CdllNodeRec stopped  = { &stopped, &stopped};

/* list of 'dead' threads that we refuse to restart */
static CdllNodeRec cemetery = { &cemetery, &cemetery };

/* repository of free nodes */
static CdllNodeRec freeList = { &freeList, &freeList };

static RtemsDebugMsg
threadOnListBwd(CdllNode list, rtems_id tid)
{
CdllNode n;
	for ( n = list->p; n != list; n = n->p ) {
		if ( ((RtemsDebugMsg)n)->tid == tid )
			return (RtemsDebugMsg)n;
	}
	return 0;
}

static inline RtemsDebugMsg
msgHeadDeQ(CdllNode list)
{
RtemsDebugMsg rval = (RtemsDebugMsg)cdll_dequeue_head(list);
	return  &rval->node == list ? 0 : rval;
}

static RtemsDebugMsg
msgAlloc()
{
RtemsDebugMsg rval = msgHeadDeQ(&freeList);
	if ( !rval && (rval = calloc(1, sizeof(RtemsDebugMsgRec))) ) {
		cdll_init_el(&rval->node);	
	}
	return rval;
}

static void
msgFree(RtemsDebugMsg msg)
{
	cdll_splerge_head(&freeList, (CdllNode)msg);
}

/************* jump buffer used for setjmp/longjmp **************************/
STATIC jmp_buf remcomEnv;

STATIC int
hex (ch)
     char ch;
{
  if ((ch >= 'a') && (ch <= 'f'))
    return (ch - 'a' + 10);
  if ((ch >= '0') && (ch <= '9'))
    return (ch - '0');
  if ((ch >= 'A') && (ch <= 'F'))
    return (ch - 'A' + 10);
  return (-1);
}

STATIC char remcomInBuffer[BUFMAX];
STATIC char remcomOutBuffer[BUFMAX];

/* scan for the sequence $<data>#<checksum>     */
#define GETCHAR() \
	  do { if ( (ch = getDebugChar()) <= 0 ) return 0; }  while (0)

STATIC unsigned char *
getpacket (void)
{
  unsigned char *buffer = &remcomInBuffer[0];
  unsigned char checksum;
  unsigned char xmitcsum;
  int count;
  int ch;

  while (1)
    {
      /* wait around for the start character, ignore all other characters */
	  do {
		GETCHAR();
      } while (ch != '$')
	;

    retry:
      checksum = 0;
      xmitcsum = -1;
      count = 0;

      /* now, read until a # or end of buffer is found */
      while (count < BUFMAX)
	{
	  GETCHAR();
	  if (ch == '$')
	    goto retry;
	  if (ch == '#')
	    break;
	  checksum = checksum + ch;
	  buffer[count] = ch;
	  count = count + 1;
	}
      buffer[count] = 0;

      if (ch == '#')
	{
	  GETCHAR();
	  xmitcsum = hex (ch) << 4;
	  GETCHAR();
	  xmitcsum += hex (ch);

	  if (checksum != xmitcsum)
	    {
	      if (rtems_remote_debug)
		{
		  fprintf (stderr,
			   "bad checksum.  My count = 0x%x, sent=0x%x. buf=%s\n",
			   checksum, xmitcsum, buffer);
		}
	      putDebugChar ('-');	/* failed checksum */
          flushDebugChars();
	    }
	  else
	    {
          unsigned char *rval;
	      putDebugChar ('+');	/* successful transfer */

	      /* if a sequence char is present, reply the sequence ID */
	      if (buffer[2] == ':')
		{
		  putDebugChar (buffer[0]);
		  putDebugChar (buffer[1]);

		  rval = &buffer[3];
		} else {
		  rval = &buffer[0];
		}
		flushDebugChars();
		return rval;
	    }
	}
    }
}

/* send the packet in buffer. */

STATIC int
putpacket (buffer)
     char *buffer;
{
  unsigned char checksum;
  int count;
  char ch;

  /*  $<packet info>#<checksum>. */
  do
    {
      putDebugChar ('$');
      checksum = 0;
      count = 0;
      while ( (ch = buffer[count]) )
	{
	  putDebugChar (ch);
	  checksum += ch;
	  count += 1;
	}

      putDebugChar ('#');
      putDebugChar (hexchars[checksum >> 4]);
      putDebugChar (hexchars[checksum % 16]);
      flushDebugChars();
	if ( rtems_remote_debug > 2 ) {
		fprintf(stderr,"Putting packet (len %i)\n",count);
	}


	  count = getDebugChar();
  } while ( count > 0 && count != '+');
  return count <= 0;
}

STATIC void
debug_error (char *format, char *parm)
{
  if (rtems_remote_debug)
    fprintf (stderr, format, parm);
}

/* convert the memory pointed to by mem into hex, placing result in buf */
/* return a pointer to the last char put in buf (null) */
STATIC char *
mem2hex (mem, buf, count)
     char *mem;
     char *buf;
     int count;
{
  int i;
  unsigned char ch;
  for (i = 0; i < count; i++)
    {
      ch = *mem++;
      *buf++ = hexchars[ch >> 4];
      *buf++ = hexchars[ch % 16];
    }
  *buf = 0;
  return (buf);
}

/* integer to BE hex; buffer must be large enough */

STATIC char *
intToHex(int i, char *buf)
{
register int j = 2*sizeof(i);

    if ( i< 0 ) {
		*buf++='-';
		i = -i;
	}
	buf[j--]=0;
	do {
		buf[j--] = hexchars[i&0xf];
		i>>=4;
	} while ( j>=0 );
	return buf+2*sizeof(i);
}

/* convert the hex array pointed to by buf into binary to be placed in mem */
/* return a pointer to the character AFTER the last byte written */
STATIC char *
hex2mem (buf, mem, count)
     char *buf;
     char *mem;
     int count;
{
  int i;
  unsigned char ch;
  for (i = 0; i < count; i++)
    {
      ch = hex (*buf++) << 4;
      ch = ch + hex (*buf++);
      *mem++ = ch;
    }
  return (mem);
}

/**********************************************/
/* WHILE WE FIND NICE HEX CHARS, BUILD AN INT */
/* RETURN NUMBER OF CHARS PROCESSED           */
/**********************************************/
STATIC int
hexToInt (char **ptr, int *intValue)
{
  int numChars = 0;
  int hexValue;

  *intValue = 0;

  while (**ptr)
    {
      hexValue = hex (**ptr);
      if (hexValue >= 0)
	{
	  *intValue = (*intValue << 4) | hexValue;
	  numChars++;
	}
      else
	break;

      (*ptr)++;
    }

  return (numChars);
}

volatile rtems_id  rtems_gdb_tid       = 0;
volatile int       rtems_gdb_sd        = -1;
volatile rtems_id  rtems_gdb_break_tid = 0;

STATIC RtemsDebugMsg	theDummy = 0;
STATIC unsigned long    dummy_frame_pc;

static volatile int      waiting = 0;

static void sowake(struct socket *so, caddr_t arg)
{
rtems_status_code sc;

	if ( waiting ) {
		sc = rtems_semaphore_flush(gdb_pending_id);
	}

}

static int resume_stopped_task(rtems_id tid, int sig)
{
RtemsDebugMsg m;
int rval, do_free;
	if ( tid ) {
		m = threadOnListBwd(&stopped, tid);
		if ( m ) {
			cdll_splerge_tail(&m->node, m->node.p);
			/* see comment below why we use 'do_free' */
			do_free = (m->frm == 0);
			rval = task_resume(m,sig);
			if (do_free) {
				m->tid = 0;
				msgFree(m);
			}
		} else {
			fprintf(stderr,"Unable to resume 0x%08x -- not found on stopped list\n", tid);
			rval = -1;
		}
		return rval;
	} else {
		rval = 0;
		/* release all currently stopped threads */
		while ( (m=msgHeadDeQ(&stopped)) ) {
			do_free = (m->frm == 0);
			/* cannot access 'msg' after resuming. If it
			 * was a 'real', i.e., non-frameless message then
			 * it lived on the stack of the to-be resumed
			 * thread.
			 */
			if ( task_resume(m, sig) ) {
fprintf(stderr,"Task resume %x FAILURE\n",m->tid);
				rval = -1;
			}
			if ( do_free ) {
				m->tid = 0;
				msgFree(m);
			}
		}
	}
	return rval;
}

static void detach_all_tasks()
{
RtemsDebugMsg msg;

	rtems_gdb_tgt_remove_all_bpnts();

	/* detach all tasks */

	/* collect all pending tasks */
	while ( (msg=getFirstMsg(0)) )
		;

	/* and resume everything */
	resume_stopped_task(0, SIGCONT);

	rtems_gdb_break_tid = 0;
}

static void cleanup_connection()
{
struct sockwakeup wkup = {0};

	if (rtems_remote_debug > 1)
		printf("Releasing connection\n");

	detach_all_tasks();

	/* make sure the callback is removed */
    setsockopt(fileno(rtems_gdb_strm), SOL_SOCKET, SO_RCVWAKEUP, &wkup, sizeof(wkup));
	fclose( rtems_gdb_strm );
	rtems_gdb_strm = 0;
}

static int
havestate(RtemsDebugMsg m)
{
	if ( TID_ANY == m->tid || TID_ALL == m->tid ) {
		strcpy(remcomOutBuffer,"E16");
		return 0;
	}
	return 1;
}

STATIC rtems_id *
get_tid_tab(rtems_id *t)
{
int                 max, cur, i, api;
Objects_Information *info;
Objects_Control		*c;
	/* count slots */
	{
again:
		/* get current estimate */
		for ( max=0, api=0; api<=OBJECTS_APIS_LAST; api++ ) {
			Objects_Information **apiinfo = _Objects_Information_table[api];
			if ( apiinfo && (info = apiinfo[1/* thread class for all APIs*/] ) )
				max += info->maximum;
		}
		t = realloc(t, sizeof(rtems_id)*(max+1));

		if ( t ) {
			cur = 0;
			_Thread_Disable_dispatch();
			for ( api=0; api<=OBJECTS_APIS_LAST; api++ ) {
				Objects_Information **apiinfo = _Objects_Information_table[api];
				if ( !apiinfo
                    || !(info = apiinfo[1/* thread class for all APIs*/] )
					|| !info->local_table )
					continue;
				for ( i=1; i<=info->maximum; i++ ) {
					if (!(c=info->local_table[i]))
						continue;
					t[cur++] = c->id;
					if ( cur >= max ) {
						/* table was extended since we determined the maximum; try again */
						_Thread_Enable_dispatch();
						goto again;
					}
				}
			}
			_Thread_Enable_dispatch();
			t[cur]=0;
		}
	}
	return t;
}

static void
dummy_thread(rtems_task_argument arg)
{
	while (1) {
#ifdef DUMMY_SUSPENDED
		rtems_task_suspend(RTEMS_SELF);
#else
		BREAKPOINT();
#endif
		sleep(1);
	}
}

static  RtemsDebugMsgRec  currentEl = {{&currentEl.node,&currentEl.node},0};

static  rtems_id        dummy_tid = 0;

static int unAttachedCmd(int ch)
{
	return 'H' == ch || 'm'==ch || 'd' == ch || 'D' == ch
           || 'q' == ch;
}

static int compileThreadExtraInfo(char *extrabuf, rtems_id tid)
{
Thread_Control    *thr;
Objects_Locations l;
States_Control    state = 0xffff;
int               pri   = 0, i = 0;

	memset(extrabuf,0,EXTRABUFSZ);
	if ( (thr=_Thread_Get( tid, &l )) ) {
		if ( OBJECTS_LOCAL == l ) {
			Objects_Information *oi;
			oi = _Objects_Get_information( tid );
			*extrabuf = '\'';
			if ( oi->is_string ) {
				if ( oi->name_length < EXTRABUFSZ ) {
					_Objects_Copy_name_string( thr->Object.name, extrabuf + 1  );
				} else {
					strcpy( extrabuf + 1, "NAME TOO LONG" ); 
				}
			} else {
				_Objects_Copy_name_raw( &thr->Object.name, extrabuf + 1, oi->name_length );
			}
			state = thr->current_state;
			pri   = thr->real_priority;
		}
		_Thread_Enable_dispatch();
		if ( OBJECTS_LOCAL != l )
			return 0;
		i = strlen(extrabuf);
		extrabuf[i++]='\'';
		while (i<8)
			extrabuf[i++]=' ';
		i+=snprintf(extrabuf+i,EXTRABUFSZ-i,"PRI: %3d STATE:", pri);
		state = state & STATES_ALL_SET;
		if ( i<EXTRABUFSZ ) {
			if ( STATES_READY == state)
				i+=sprintf(extrabuf+i," ready");
			else {
			if ( STATES_DORMANT   & state && i < EXTRABUFSZ ) {
				i+=sprintf(extrabuf+i," dorm");
				state &= ~STATES_DORMANT;
			}
			if ( STATES_SUSPENDED & state && i < EXTRABUFSZ ) {
				i+=sprintf(extrabuf+i," susp");
				state &= ~STATES_SUSPENDED;
			}
			if ( STATES_TRANSIENT & state && i < EXTRABUFSZ ) {
				i+=sprintf(extrabuf+i," trans");
				state &= ~STATES_TRANSIENT;
			}
			if ( STATES_BLOCKED & state && i < EXTRABUFSZ ) {
				i+=sprintf(extrabuf+i," BLOCKED - ");
				if ( STATES_DELAYING  & state && i < EXTRABUFSZ )
					i+=sprintf(extrabuf+i," delyd");
				if ( STATES_INTERRUPTIBLE_BY_SIGNAL  & state && i < EXTRABUFSZ )
					i+=sprintf(extrabuf+i," interruptible");
				if ( STATES_WAITING_FOR_TIME & state && i < EXTRABUFSZ )
						i+=sprintf(extrabuf+i," time");
			if ( STATES_WAITING_FOR_BUFFER & state && i < EXTRABUFSZ )
					i+=sprintf(extrabuf+i," buf");
				if ( STATES_WAITING_FOR_SEGMENT & state && i < EXTRABUFSZ )
					i+=sprintf(extrabuf+i," seg");
				if ( STATES_WAITING_FOR_MESSAGE & state && i < EXTRABUFSZ )
					i+=sprintf(extrabuf+i," msg");
				if ( STATES_WAITING_FOR_EVENT & state && i < EXTRABUFSZ )
					i+=sprintf(extrabuf+i," evt");
				if ( STATES_WAITING_FOR_SEMAPHORE & state && i < EXTRABUFSZ )
					i+=sprintf(extrabuf+i," sem");
				if ( STATES_WAITING_FOR_MUTEX & state && i < EXTRABUFSZ )
					i+=sprintf(extrabuf+i," mtx");
				if ( STATES_WAITING_FOR_CONDITION_VARIABLE & state && i < EXTRABUFSZ )
					i+=sprintf(extrabuf+i," cndv");
				if ( STATES_WAITING_FOR_JOIN_AT_EXIT & state && i < EXTRABUFSZ )
					i+=sprintf(extrabuf+i," join");
				if ( STATES_WAITING_FOR_RPC_REPLY & state && i < EXTRABUFSZ )
					i+=sprintf(extrabuf+i," rpc");
				if ( STATES_WAITING_FOR_PERIOD & state && i < EXTRABUFSZ )
					i+=sprintf(extrabuf+i," perio");
				if ( STATES_WAITING_FOR_SIGNAL & state && i < EXTRABUFSZ )
					i+=sprintf(extrabuf+i," sig");
				state &= ~STATES_BLOCKED;
			}
			}
			if ( state && i < EXTRABUFSZ ) {
				i+=snprintf(extrabuf+i, EXTRABUFSZ-i, "?? (0x%x)", state);
			}
		}
	}
	return i;
}
/*
 * This function does all command processing for interfacing to gdb.
 */
STATIC void
rtems_gdb_daemon (rtems_task_argument arg)
{
  char              *ptr, *pto;
  const char        *pfrom;
  char              *chrbuf = 0;
  int               sd,regno,i,j;
  RtemsDebugMsg     current = 0;
  rtems_status_code sc;
  rtems_id          *tid_tab = calloc(1,sizeof(rtems_id)), tid, cont_tid;
  int               tidx = 0;
  int               ehandler_installed=0;
  CexpModule		mod   = 0;
  CexpSym           *psectsyms = 0;
  int				addr,len;
  /* startup / initialization */
  {
    if ( RTEMS_SUCCESSFUL !=
		 ( sc = rtems_semaphore_create(
					rtems_build_name( 'g','d','b','s' ),
					0,
					RTEMS_FIFO | RTEMS_COUNTING_SEMAPHORE,
					0,
					&gdb_pending_id ) ) ) {
		gdb_pending_id = 0;
		rtems_error( sc, "GDBd: unable to create semaphore" );
		goto cleanup;
	}
	if ( !(chrbuf = malloc(CHRBUFSZ)) ) {
		fprintf(stderr,"no memory\n");
		goto cleanup;
	}

    /* create socket */
    rtems_gdb_sd = socket(PF_INET, SOCK_STREAM, 0);
	if ( rtems_gdb_sd < 0 ) {
		perror("GDB daemon: socket");
		goto cleanup;
	}
	{
    int                arg = 1;
    struct sockaddr_in srv; 

      setsockopt(rtems_gdb_sd, SOL_SOCKET, SO_KEEPALIVE, &arg, sizeof(arg));
      setsockopt(rtems_gdb_sd, SOL_SOCKET, SO_REUSEADDR, &arg, sizeof(arg));

      memset(&srv, 0, sizeof(srv));
      srv.sin_family = AF_INET;
      srv.sin_port   = htons(RTEMS_GDB_PORT);
      arg            = sizeof(srv);
      if ( bind(rtems_gdb_sd,(struct sockaddr *)&srv,arg)<0 ) {
        perror("GDB daemon: bind");
		goto cleanup;
      };
    }
	if ( listen(rtems_gdb_sd, 1) ) {
		perror("GDB daemon: listen");
		goto cleanup;
	}
	if (rtems_debug_install_ehandler(1))
		goto cleanup;
	ehandler_installed=1;
	if ( !(dummy_tid = thread_helper("GDBh", 200, 20000+RTEMS_MINIMUM_STACK_SIZE, dummy_thread, 0)) )
		goto cleanup;
  }

  initialized = 1;

  while (initialized) {

	/* synchronize with dummy task */
	if ( !theDummy ) {
		getFirstMsg(1);
		assert( theDummy );
	}
	dummy_frame_pc = rtems_gdb_tgt_get_pc( theDummy );
#ifndef ONETHREAD_TEST
	current = theDummy;
#else
	current = 0;
#endif

	{
	struct sockaddr_in a;
    struct sockwakeup  wkup;
	size_t             a_s = sizeof(a);
	if ( (sd = accept(rtems_gdb_sd, (struct sockaddr *)&a, &a_s)) < 0 ) {
		perror("GDB daemon: accept");
		goto cleanup;
	}
    wkup.sw_pfn = sowake;
    wkup.sw_arg = (caddr_t)0;
    setsockopt(sd, SOL_SOCKET, SO_RCVWAKEUP, &wkup, sizeof(wkup));
	}
	if ( !(rtems_gdb_strm = fdopen(sd, "r+")) ) {
		perror("GDB daemon: unable to open stream");
		close(sd);
		goto cleanup;
	}

	cont_tid = 0;

	while ( (ptr = getpacket()) ) {

    remcomOutBuffer[0] = 0;

	if (rtems_remote_debug > 2) {
		printf("Got packet '%c' \n", *ptr);
	}

	if ( current || unAttachedCmd(*ptr) ) {

    switch (*ptr++)
	{
	default:
	  remcomOutBuffer[0] = 0;
	  break;

	case '?':
	  sprintf(remcomOutBuffer,"T%02xthread:%08x;",current->sig, current->tid);
	  break;

	case 'd':
	  rtems_remote_debug = !(rtems_remote_debug);	/* toggle debug flag */
	  break;

	case 'D':
      strcpy(remcomOutBuffer,"OK");
#ifndef ONETHREAD_TEST
	  detach_all_tasks();
	  current = 0;
	  rtems_gdb_break_tid = 0;
#else
	  goto cleanup_connection();
#endif
	break;

	case 'g':		/* return the value of the CPU registers */
	  if (!havestate(current))
		break;
	  rtems_gdb_tgt_f2r(chrbuf, current);
	  mem2hex ((char *) chrbuf, remcomOutBuffer, NUMREGBYTES);
	  break;

	case 'G':		/* set the value of the CPU registers - return OK */
	  if (!havestate(current))
		break;
	  hex2mem (ptr, (char *) chrbuf, NUMREGBYTES);
	  rtems_gdb_tgt_r2f(current, chrbuf);
	  strcpy (remcomOutBuffer, "OK");
	  break;

    case 'H':
      {
		tid = strtol(ptr+1,0,16);
		if ( rtems_remote_debug ) {
			printf("New 'H%c' thread id set: 0x%08x\n",*ptr,tid);
		}
#ifndef ONETHREAD_TEST
	  	if ( 'c' == *ptr ) {
			/* We actually have slightly different semantics.
			 * In our case, this TID tells us whether we break
			 * on this tid only or on any arbitrary one
			 */
			/* NOTE NOTE: This currently does NOT work -- GDB inserts
			rtems_gdb_break_tid = (TID_ALL == tid || TID_ANY == tid) ? 0 : tid;
			 *            breakpoints prior to sending the thread id :-(
			 *            maybe we should globally enable breakpoints
			 *            only when we 'continue' or 'step'
			 */
			cont_tid = tid;
	  	} else if ( 'g' == *ptr ) {
			if ( (TID_ALL == tid || TID_ANY == tid) )
				tid = current->tid ? current->tid : dummy_tid;
			else if ( rtems_gdb_tid == tid )
				tid = dummy_tid;
			if ( current->tid == tid )
				break;
			current = task_switch_to(current, tid);
	  	}
#else
		if ( rtems_gdb_break_tid && tid != rtems_gdb_break_tid ) {
			strcpy(remcomOutBuffer,"E0D");
		} else if ( !current ) {
			/* "attach" */
			if ( tid ) {
				rtems_gdb_break_tid = tid;
				current = task_switch_to( 0, tid );
			} else {
				/* wait for target */
				if ( pendSomethingHappening(&current, tid, remcomOutBuffer) < 0 ) {
					/* daemon killed */
					goto release_connection;
				}

			}
		}
#endif
	  }
    break;

	  /* mAA..AA,LLLL  Read LLLL bytes at address AA..AA */
	case 'm':
	  if (setjmp (remcomEnv) == 0)
	    {
	      /* TRY TO READ %x,%x.  IF SUCCEED, SET PTR = 0 */
	      if (hexToInt (&ptr, &addr))
		if (*(ptr++) == ',')
		  if (hexToInt (&ptr, &len))
		    {
		      ptr = 0;
		      mem2hex ((char *) addr, remcomOutBuffer, len);
		    }

	      if (ptr)
		{
		  strcpy (remcomOutBuffer, "E01");
		}
	    }
	  else
	    {
	      strcpy (remcomOutBuffer, "E03");
	      debug_error ("%s\n","bus error");
	    }

	  break;

	  /* MAA..AA,LLLL: Write LLLL bytes at address AA.AA return OK */
	case 'M':
	  if (setjmp (remcomEnv) == 0)
	    {
	      /* TRY TO WRITE '%x,%x:'.  IF SUCCEED, SET PTR = 0 */
	      if (hexToInt (&ptr, &addr))
		if (*(ptr++) == ',')
		  if (hexToInt (&ptr, &len))
		    if (*(ptr++) == ':')
		      {
			hex2mem (ptr, (char *) addr, len);
			ptr = 0;
			strcpy (remcomOutBuffer, "OK");
		      }
	      if (ptr)
		{
		  strcpy (remcomOutBuffer, "E02");
		}
	    }
	  else
	    {
	      strcpy (remcomOutBuffer, "E03");
	      debug_error ("%s\n","bus error");
	    }

	  break;

	case 's': /* trace */
	case 'c':
		{
		int contsig = 's' == *(ptr-1) ? SIGTRAP : SIGCONT;

		if ( hexToInt(&ptr, &i) ) { /* optional addr arg */
			if ( current ) {
				if ( !current->frm ) {
					/* refuse if we don't have a 'real' frame */
					strcpy(remcomOutBuffer,"E0D");
					break;
				}
				rtems_gdb_tgt_set_pc(current, i);
			}
		}

		if ( current ) {
			tid  = current->tid;
			i   = resume_stopped_task(cont_tid, contsig);
		} else {
			i   = 0;
			tid = rtems_gdb_break_tid;
		}
		}

		if ( -2 == i ) {
			/* target doesn't know how to start single-stepping on
			 * a suspended thread (which has no real frame)
			 */
			strcpy(remcomOutBuffer,"E0D");
			break;
		} else if ( 0 == i )
			current = 0;

		if ( pendSomethingHappening(&current, tid, remcomOutBuffer) < 0 )
			/* daemon killed */
			goto release_connection;

	break;

	case 'P':
	  strcpy(remcomOutBuffer,"E16");
	  if (   !havestate(current)
          || !hexToInt(&ptr, &regno)
          || '=' != *ptr++
		  || (i = rtems_gdb_tgt_regoff(regno, &j)) < 0 )
		break;
		
	  rtems_gdb_tgt_f2r((char*)chrbuf,current);
	  hex2mem (ptr, ((char*)chrbuf) + j, i);
	  rtems_gdb_tgt_r2f(current, chrbuf);
	  strcpy (remcomOutBuffer, "OK");
	  break;

	case 'q':
      if ( !strcmp(ptr,"Offsets") ) {
		/* ignore; GDB should use values from executable file */
	  } else if ( !strncmp(ptr,"CRC:",4) ) {
		ptr+=4;
		if ( !hexToInt(&ptr,&addr) || ','!=*ptr++ || !hexToInt(&ptr,&len) ) {
			strcpy(remcomOutBuffer,"E0D");
		} else {
			if ( 0 == setjmp(remcomEnv) ) {
				/* try to compute crc */
				sprintf(remcomOutBuffer,"C%x",crc32((char*)addr, len, -1));
			} else {
	      		strcpy (remcomOutBuffer, "E03");
	      		debug_error ("%s\n","bus error");
			}
		}
	  } else if ( !strcmp(ptr+1,"ThreadInfo") ) {
		if ( 'f' == *ptr ) {
			tidx = 0;
			/* TODO get thread snapshot */
			tid_tab = get_tid_tab(tid_tab);
		}
		pto    = remcomOutBuffer;
		if ( !tid_tab[tidx] ) {
			strcpy(pto,"l");
		} else {
			while ( tid_tab[tidx] && pto < remcomOutBuffer + sizeof(remcomOutBuffer) - 20 ) {
				*pto++ = ',';
				pto    = intToHex(tid_tab[tidx++], pto);
			}
			*pto = 0;
			remcomOutBuffer[0]='m';
		}
	  } else if ( !strncmp(ptr,"ThreadExtraInfo",15) ) {
		ptr+=15;
		if ( ','== *ptr ) {
			tid = strtol(++ptr,0,16);
			i = compileThreadExtraInfo(chrbuf, tid);
			if (*chrbuf)
	  			mem2hex (chrbuf, remcomOutBuffer, i+1);
		}
	  } else if ( !strcmp(ptr+1,"CexpFileList") ) {
	    if ( 'f' == *ptr ) {
			mod = cexpSystemModule->next;
		}
		if ( mod ) {
			pto    = remcomOutBuffer;
			*pto++ = 'm';
			pto    = intToHex(mod->text_vma, pto); 
			*pto++ = ',';
			if ( !(pfrom = strrchr(mod->name,'/')) )
				pfrom = mod->name;
			else
				pfrom++;
			if ( strlen(pfrom) > BUFMAX - 15 )
				strcpy(remcomOutBuffer,"E24");
			else
				strcpy(pto,pfrom);
			mod = mod->next;
		} else {
			strcpy(remcomOutBuffer,"l");
		}
#define SECTLIST_STR "CexpSectionList"
	  } else if ( !strncmp(ptr+1,SECTLIST_STR,strlen(SECTLIST_STR)) ) {
	    if ( 'f' == *ptr ) {
			ptr+=1+strlen(SECTLIST_STR);
			psectsyms = 0;
			if ( ',' != *ptr || !*(ptr+1) ) {
				strcpy(remcomOutBuffer,"E16");
			} else {
				mod = cexpModuleFindByName(++ptr, CEXP_FILE_QUIET);
				if ( !mod ) {
					strcpy(remcomOutBuffer,"E02");
					break;
				} else {
					psectsyms = mod->section_syms;
					mod = 0;
				}
			}
		}
		if ( psectsyms && *psectsyms ) {
			pto    = remcomOutBuffer;
			*pto++ = 'm';
			pto    = intToHex((int)(*psectsyms)->value.ptv, pto); 
			*pto++ = ',';
			pfrom  = (*psectsyms)->name;
			if ( strlen(pfrom) > BUFMAX - 15 )
				strcpy(remcomOutBuffer,"E24");
			else
				strcpy(pto,pfrom);
			psectsyms++;
		} else {
			strcpy(remcomOutBuffer,"l");
		}
	  }

	  break;

	  case 'T':
		{
		rtems_id tid;
			strcpy(remcomOutBuffer,"E01");
			tid = strtol(ptr,0,16);
			/* use a cheap call to find out if this is still alive ... */
			sc = rtems_task_is_suspended(tid);
			if ( RTEMS_SUCCESSFUL == sc || RTEMS_ALREADY_SUSPENDED == sc )
				strcpy(remcomOutBuffer,"OK");
		}	
	  break;

	  case 'z':
	  case 'Z':
		{
		char *op = ptr++-1;
		if (   ',' != *ptr++ || !hexToInt(&ptr,&addr)
            || ',' != *ptr++ || !hexToInt(&ptr,&len) 
			)
		break;

		switch ( op[1] ) {
			case '0':
			/* software breakpoint */
			if ( 0 == setjmp(remcomEnv) ) {
				/* try to write breakpoint */
				rtems_gdb_tgt_insdel_breakpoint('Z'==op[0],addr,len);
				strcpy(remcomOutBuffer,"OK");
			} else {
	      		strcpy (remcomOutBuffer, "E03");
	      		debug_error ("%s\n","bus error");
			}
			break;
			default:	
				strcpy (remcomOutBuffer, "E16");
			break;
		}
		}
	  break;

	}			/* switch */
	}

      /* reply to the request */
      if (putpacket (remcomOutBuffer))
		goto release_connection;
  } /* interpreter loop */
release_connection:
  /* make sure attached thread continues */
#ifdef OBSOLETE
  if ( current )
  	task_resume( current, SIGCONT );
#endif
  cleanup_connection();

  }

/* shutdown */
cleanup:
  if ( gdb_pending_id )
	rtems_semaphore_delete( gdb_pending_id );
  if (dummy_tid)
  	rtems_task_delete(dummy_tid);
  if ( ehandler_installed ) {
	rtems_debug_install_ehandler(0);
  }
  if ( rtems_gdb_strm ) {
	fclose(rtems_gdb_strm);
	rtems_gdb_strm = 0;
  }
  if ( 0 <= rtems_gdb_sd ) {
    close(rtems_gdb_sd);
  }
  free( chrbuf );
  free( tid_tab );

  rtems_gdb_tid=0;
  rtems_task_delete(RTEMS_SELF);
}

/* This function will generate a breakpoint exception.  It is used at the
   beginning of a program to sync up with a debugger and can be used
   otherwise as a quick means to stop program execution and "break" into
   the debugger. */

void
rtems_debug_breakpoint ()
{
  if (initialized)
    BREAKPOINT ();
}

void rtems_debug_handle_exception(int signo)
{
	longjmp(remcomEnv,1);
}

static rtems_id
thread_helper(char *nm, int pri, int stack, void (*fn)(rtems_task_argument), rtems_task_argument arg)
{
char              buf[4];
rtems_status_code sc;
rtems_id          rval = 0;


	if ( 0==pri )
		pri = 100;

	if ( 0==stack )
		stack = RTEMS_MINIMUM_STACK_SIZE;

	memset(buf,'x',sizeof(buf));
	if (nm)
		strncpy(buf,nm,4);
	else
		nm="<NULL>";

	sc = rtems_task_create(	
			rtems_build_name(buf[0],buf[1],buf[2],buf[3]),
			pri,
			stack,
			RTEMS_DEFAULT_MODES,
			RTEMS_LOCAL | RTEMS_FLOATING_POINT,
			&rval);
	if ( RTEMS_SUCCESSFUL != sc ) {
		rtems_error(sc, "Creating task '%s'",nm);
		goto cleanup;
	}

	sc = rtems_task_start(rval, fn, arg);
	if ( RTEMS_SUCCESSFUL != sc ) {
		rtems_error(sc, "Starting task '%s'",nm);
		rtems_task_delete(rval);
		goto cleanup;
	}

cleanup:
	if ( RTEMS_SUCCESSFUL != sc ) {
		rval = 0;
	}
	return rval;
}

void blah()
{
	while (1) {
		sleep(8);
		asm volatile("sc");
	}
	rtems_task_delete(RTEMS_SELF);
}

int
rtems_debug_start(int pri)
{

	rtems_gdb_tid = thread_helper("GDBd", 20, 20000+RTEMS_MINIMUM_STACK_SIZE, rtems_gdb_daemon, 0);
#if 1
	thread_helper("blah", 200, RTEMS_MINIMUM_STACK_SIZE, blah, 0);
#endif

	return !rtems_gdb_tid;
}

int
_cexpModuleFinalize(void *h)
{
RtemsDebugMsg n;
	if ( rtems_gdb_tid ) {
		fprintf(stderr,"GDB daemon still running; refuse to unload\n");
		return -1;
	}
	
	while ( (n = msgHeadDeQ(&freeList)) )
		free(n);
	return 0;
}


struct sockaddr_in blahaddr = {0};

void
_cexpModuleInitialize(void *h)
{
    blahaddr.sin_family = AF_INET;
    blahaddr.sin_port   = htons(RTEMS_GDB_PORT);

    {
      /* Initialize the CRC table and the decoding table. */
	int i, j;
	unsigned int c;
                                                                                                                                                         
	for (i = 0; i < 256; i++) {
		for (c = i << 24, j = 8; j > 0; --j)
			c = c & 0x80000000 ? (c << 1) ^ 0x04c11db7 : (c << 1);
		crc32_table[i] = c;
	}
    }

 	rtems_debug_start(40);
}

void
rtems_debug_stop()
{
int  sd;

	/* enqueue a special message */
	initialized = 0;
	rtems_semaphore_flush( gdb_pending_id );

	sd = rtems_gdb_sd;
	rtems_gdb_sd = -1;
	if ( sd >= 0 )
		close(sd);
}

/* restart the thread provided that it exists and
 * isn't suspended due to a 'real' exception (as opposed to
 * a breakpoint).
 */
static int
task_resume(RtemsDebugMsg msg, int sig)
{
rtems_status_code sc = -1;
	if ( msg->tid ) {

		/* never really resume the dummy tid */
		if ( msg->tid == dummy_tid ) {
		    if ( dummy_frame_pc == rtems_gdb_tgt_get_pc( msg ) ) {
				theDummy = msg;
				return 0;
			} else {
				theDummy = 0;
fprintf(stderr,"STARTING DUMMY with sig %i\n",msg->sig);
				msg->sig = SIGTRAP;
			}
		}
		/* if we attached to an already sleeping thread, don't resume
		 * don't resume DEAD threads that were suspended due to memory
		 * faults etc. either
		 */
		if ( SIGINT == msg->sig || (msg->frm && SIGTRAP == msg->sig) ) {
			msg->contSig = sig;
			assert(msg->node.p == msg->node.n && msg->node.p == &msg->node);
			/* ask the target specific code to help if they want to single
			 * step a frame-less task
			 */
			if ( msg->frm
			    || SIGCONT == sig
      /* HMMM - We can't just change the state in the TCB.
	   *        What if we the thread is soundly asleep? We
	   *        currently have no provision to undo the changes
	   *        made by tgt_single_step()...
				|| 0 == rtems_gdb_tgt_single_step(msg)
	   */
			   ) {
				printf("Resuming 0x%08x with sig %i\n",msg->tid, msg->contSig);
				sc = rtems_task_resume(msg->tid);
			}
			return RTEMS_SUCCESSFUL == sc ? 0 : -2;
		} else {
			/* add to cemetery if not there already */
			if ( &msg->node == msg->node.p )
				cdll_splerge_tail(&cemetery, &msg->node);
			msg->contSig = 0;
		}
	}
	return -1;
}


static RtemsDebugMsg
task_switch_to(RtemsDebugMsg cur, rtems_id new_tid)
{
printf("SWITCH 0x%08x -> 0x%08x\n", cur ? cur->tid : 0, new_tid);

	if ( cur ) {
		if ( cur->tid == new_tid )
			return cur;
#ifdef OBSOLETE
		task_resume(cur, SIGCONT);
#endif
	}

	if ( new_tid == dummy_tid && theDummy ) {
		cur = theDummy;
		if ( ! threadOnListBwd(&stopped, new_tid) ) {
			cdll_splerge_head(&stopped, (CdllNode)cur);
		}
		return cur;
	}

#ifdef OBSOLETE
	cur = &currentEl;

	memset(cur, 0, sizeof(*cur));
	cdll_init_el(&cur->node);

	cur->tid = new_tid;
#endif

	if ( new_tid ) {
		rtems_status_code sc;
		switch ( (sc = rtems_task_suspend( new_tid )) ) {
			case RTEMS_ALREADY_SUSPENDED:
				/* Hmm - could be that this is a task that is in
				 * the list somewhere.
				 * NOTE: it is NOT necessary to lock the list while
				 *       we scan it since new elements could ONLY be
				 *		 added _after_ the current tail AND the target
				 *       we're looking for is already suspended and
				 *       hence somewhere between the anchor and the
				 *       current tail;
				 */
				{
				RtemsDebugMsg t;
					if ( (t = threadOnListBwd(&anchor, new_tid)) ) {
						unsigned long flags;
						/* found; dequeue and return */
						rtems_interrupt_disable(flags);
						cdll_splerge_tail(&t->node, t->node.p);
						rtems_interrupt_enable(flags);
						assert( RTEMS_SUCCESSFUL == rtems_semaphore_obtain( gdb_pending_id, RTEMS_NO_WAIT, RTEMS_NO_TIMEOUT ) );
						SEMA_DEC();
						cur = t;
						break;
					} else if ( ( t = threadOnListBwd(&cemetery, new_tid) ) ) {
						cur = t;
						break;
					} else if ( ( t = threadOnListBwd(&stopped, new_tid) ) ) {
						cur = t;
						break;
					} else {
						/* hit an already suspended thread
						 * FALL THROUGH and get a new (frameless) node
						 */
					}
				}
				/* FALL THRU */

			case RTEMS_SUCCESSFUL:
				/* We just stopped this thread */
				cur = msgAlloc();
				cur->sig = SIGINT;
				cur->tid = new_tid;
				break;

				
			default:
				cur->tid = 0;
				rtems_error(sc, "suspending target thread 0x%08x failed", new_tid);
				/* thread might have gone away; attach to helper */
				cur = theDummy; theDummy = 0;
			break;
		}
	}
	if ( cur->tid == dummy_tid ) {
		assert( !theDummy );
		theDummy = cur;
	}
	/* bring to head of stopped list */
	if ( threadOnListBwd(&stopped, cur->tid) ) {
		/* remove */
		cdll_splerge_tail(&cur->node, cur->node.p);
	}
	/* add to head */
	cdll_splerge_head(&stopped, (CdllNode)cur);
return cur;
}

/* this is called from exception handler (ISR) context !! */
void rtems_debug_notify_and_suspend(RtemsDebugMsg msg)
{
	cdll_init_el(&msg->node);

#ifndef ONETHREAD_TEST
printk("NOTIFY with sig %i\n",msg->sig);
	if ( SIGCHLD == msg->sig ) {
		if ( rtems_gdb_break_tid && rtems_gdb_break_tid != msg->tid ) {
		/* breakpoint hit; only stop if thread matches */
			msg->contSig = SIGCONT;
			return;
		} else {
			msg->sig = SIGTRAP;
		}
	}
	/* hook into the list */
	cdll_splerge_tail(&anchor, &msg->node);

	/* notify the daemon that a stopped thread is available */
	rtems_semaphore_release(gdb_pending_id);
	SEMA_INC();
#else
	switch ( msg->sig ) {
		case SIGCHLD:
			/* breakpoint hit; only stop if thread matches */
			if ( !rtems_gdb_break_tid )
				rtems_gdb_break_tid = msg->tid;
			else if ( rtems_gdb_break_tid != msg->tid ) {
				msg->contSig = SIGCONT;
				return;
			}
			msg->sig = SIGTRAP;
			
			/* fall thru */
		case SIGTRAP: /* single step tracing */
			/* hook into the list */
			cdll_splerge_tail(&anchor, &msg->node);

			/* notify the daemon that a stopped thread is available */
			rtems_semaphore_release(gdb_pending_id);
			SEMA_INC();

			break;

		default:
			/* save dead thread in the cemetery */
			cdll_splerge_tail(&cemetery, &msg->node);
		break;
	}
#endif

	/* hackish but it should work:
	 * rtems_task_suspend should work for other APIs also...
	 * probably should check for 'local' node.
	 */
	rtems_task_suspend( msg->tid );
}

static RtemsDebugMsg getFirstMsg(int block)
{
RtemsDebugMsg		msg;
unsigned long		flags;
rtems_status_code	sc;

	if ( block ) {
		sc = rtems_semaphore_obtain(gdb_pending_id, RTEMS_WAIT, RTEMS_NO_TIMEOUT);
		if ( RTEMS_UNSATISFIED == sc ) {
			/* someone interrupted us by flushing the semaphore */
			return 0;
		} else {
			assert( RTEMS_SUCCESSFUL == sc );
			SEMA_DEC();
		}
	}

	rtems_interrupt_disable(flags);
	msg = msgHeadDeQ(&anchor);
	rtems_interrupt_enable(flags);

	if ( !msg )
		return 0;

	if ( !block ) {
		assert( RTEMS_SUCCESSFUL == rtems_semaphore_obtain( gdb_pending_id, RTEMS_NO_WAIT, RTEMS_NO_TIMEOUT) );
		SEMA_DEC();
	}
	if ( msg->tid == dummy_tid ) {
		assert( !theDummy );
		theDummy = msg;
	}
	assert( ! threadOnListBwd(&stopped, msg->tid) );
	cdll_splerge_head(&stopped, &msg->node);
	return msg;
}

/* obtain the TCB of a thread.
 * NOTE that thread dispatching is enabled
 *      if this operation is successful
 *      (and disabled if unsuccessful)
 */

Thread_Control *
rtems_gdb_get_tcb_dispatch_off(rtems_id tid)
{
Objects_Locations	loc;
Thread_Control		*tcb = 0;

	if ( !tid )
		return 0;

	tcb = _Thread_Get(tid, &loc);

    if (OBJECTS_LOCAL!=loc || !tcb) {
		if (tcb)
			_Thread_Enable_dispatch();
        fprintf(stderr,"Id %x not found on local node\n",tid);
    }
	return tcb;
}

static int
pendSomethingHappening(RtemsDebugMsg *pcurrent, int tid, char *buf)
{
RtemsDebugMsg msg;

  do {
	/* check if there's another message pending
	 * wait only if we succeeded in resuming the
	 * current thread!
     */

	/* tiny chances for a race condition here -- if they hit the
	 * button before we set the flag
	 */

	waiting = 1;
	msg = getFirstMsg( 0 == *pcurrent );
	waiting = 0;

	if ( !initialized ) {
		printf("Daemon killed;\n");
		return -1;
	}

	if ( msg ) {
		*pcurrent = msg;
	} else {
		/* no new message; two possibilities:
		 * a) current == 0 which means that we
		 *    successfully resumed and hence waited
		 *    -> wait interrupted.
		 * b) current != 0 -> no wait and no other
		 *    thread pending in queue
		 */

		if ( ! *pcurrent ) {
			printf("net event\n");
			/* should be '\003' */
			getDebugChar();
			/* stop the current thread */
			if ( !tid ) {
				/* nothing attached yet */
				strcpy(buf,"X03");
				return 1;
			}
  			*pcurrent = task_switch_to(*pcurrent, tid);
			(*pcurrent)->sig = SIGINT;
		}
		/* else
		 * couldn't restart the thread. It's dead
		 * or was already suspended; since there were
		 * no messages pending, we return the old signal status
		 */
	}
		/* another thread got a signal */
  } while ( !*pcurrent );
  if ( !threadOnListBwd(&stopped, (*pcurrent)->tid ) ) {
	fprintf(stderr,"OOPS: msg %x, tid %x stoppedp %x\n",msg,(*pcurrent)->tid, stopped.p);
  }
  assert( threadOnListBwd(&stopped, (*pcurrent)->tid) );
  sprintf(buf,"T%02xthread:%08x;",(*pcurrent)->sig, (*pcurrent)->tid);
return 0;
}


