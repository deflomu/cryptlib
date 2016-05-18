/****************************************************************************
*																			*
*						  Unix Randomness-Gathering Code					*
*	Copyright Peter Gutmann, Paul Kendall, and Chris Wedgwood 1996-2015		*
*																			*
****************************************************************************/

/* This module is part of the cryptlib continuously seeded pseudorandom
   number generator.  For usage conditions, see random.c */

/* Define the following to print diagnostic information on where randomness
   is coming from */

/* #define DEBUG_RANDOM	*/

/* Comment out the following to disable printed warnings about possible
   conflicts with signal handlers and other system services */

#define DEBUG_CONFLICTS

/* General includes */

#if defined( __GNUC__ )
  #define _GNU_SOURCE
#endif /* Needed for newer functions like setresuid() */
#include <stdio.h>
#include <time.h>
#include "crypt.h"
#include "random/random.h"

/* Unix and Unix-like systems share the same makefile, make sure that the
   user isn't trying to use the Unix randomness code under a non-Unix (but
   Unix-like) system.  This would be pretty unlikely since the makefile
   automatically adjusts itself based on the environment it's running in,
   but we use the following safety check just in case.  We have to perform
   this check before we try any includes because Unix and the Unix-like
   systems don't have the same header files */

#ifdef __BEOS__
  #error For the BeOS build you need to edit $MISCOBJS in the makefile to use 'beos' and not 'unix'
#endif /* BeOS has its own randomness-gathering file */
#ifdef __ECOS__
  #error For the eCOS build you need to edit $MISCOBJS in the makefile to use 'ecos' and not 'unix'
#endif /* eCOS has its own randomness-gathering file */
#ifdef __ITRON__
  #error For the uITRON build you need to edit $MISCOBJS in the makefile to use 'itron' and not 'unix'
#endif /* uITRON has its own randomness-gathering file */
#ifdef __PALMSOURCE__
  #error For the PalmOS build you need to edit $MISCOBJS in the makefile to use 'palmos' and not 'unix'
#endif /* PalmOS has its own randomness-gathering file */
#ifdef __RTEMS__
  #error For the RTEMS build you need to edit $MISCOBJS in the makefile to use 'rtems' and not 'unix'
#endif /* RTEMS has its own randomness-gathering file */
#if defined( __TANDEM_NSK__ ) || defined( __TANDEM_OSS__ )
  #error For the Tandem build you need to edit $MISCOBJS in the makefile to use 'tandem' and not 'unix'
#endif /* Tandem OSS has its own randomness-gathering file */
#if defined( __VxWorks__ )
  #error For the VxWorks build you need to edit $MISCOBJS in the makefile to use 'vxworks' and not 'unix'
#endif /* VxWorks has its own randomness-gathering file */
#if defined( __XMK__ )
  #error For the Xilinx XMK build you need to edit $MISCOBJS in the makefile to use 'xmk' and not 'unix'
#endif /* XMK has its own randomness-gathering file */

/* Some systems built on top of Unix kernels and/or Unix-like systems don't 
   support certain functionality like the SYSV shared memory that's used for 
   last-line-of-defence entropy polling, or only support it in an erratic 
   manner that we can't rely on.  For these systems we replace the shared-
   memory-based polling with a stub the prints an error message for the
   caller */

#if defined( __Android__ ) || ( defined( __QNX__ ) && OSVERSION <= 4 )
  #define NO_SYSV_SHAREDMEM
#endif /* Android || QNX <= 4.x */

/* OS-specific includes */

#if defined( __hpux ) && ( OSVERSION >= 10 )
  #define _XOPEN_SOURCE_EXTENDED
#endif /* Workaround for inconsistent PHUX networking headers */
#include <unistd.h>
#include <errno.h>
#include <fcntl.h>
#include <pwd.h>
#if !( defined( __QNX__ ) || defined( __MVS__ ) )
  #include <sys/errno.h>
  #include <sys/ipc.h>
#endif /* !( QNX || MVS ) */
#include <sys/time.h>		/* SCO and SunOS need this before resource.h */
#ifndef __QNX__
  #if defined( _MPRAS ) && !( defined( _XOPEN_SOURCE ) && \
	  defined( __XOPEN_SOURCE_EXTENDED ) )
	/* On MP-RAS 3.02, the X/Open test macros must be set to include
	   getrusage(). */
	#define _XOPEN_SOURCE 1
	#define _XOPEN_SOURCE_EXTENDED 1
	#define MPRAS_XOPEN_DEFINES
  #endif /* MP-RAS */
  #include <sys/resource.h>
  #if defined( MPRAS_XOPEN_DEFINES )
	#undef _XOPEN_SOURCE
	#undef _XOPEN_SOURCE_EXTENDED
	#undef MPRAS_XOPEN_DEFINES
  #endif /* MP-RAS */
#endif /* QNX */
#ifdef __linux__ 
  #include <linux/random.h>
#endif /* Linux */
#ifdef __iOS__ 
  #include <Security/SecRandom.h>
#endif /* __iOS__  */
#if defined( _AIX ) || defined( __QNX__ )
  #include <sys/select.h>
#endif /* Aches || QNX */
#ifdef _AIX
  #include <sys/systemcfg.h>
#endif /* Aches */
#ifdef __CYGWIN__
  #include <signal.h>
  #include <sys/ipc.h>
  #include <sys/sem.h>
  #include <sys/shm.h>
#endif /* CYGWIN */
#if !( defined( __Android__ ) || defined( __CYGWIN__ ) || defined( __QNX__ ) )
  #include <sys/shm.h>
#endif /* !( __Android__  || Cygwin || QNX ) */
#if defined( __linux__ ) && ( defined(__i386__) || defined(__x86_64__) )
  #include <sys/timex.h>	/* For rdtsc() */
#endif /* Linux on x86 */
#if defined( __FreeBSD__ ) || defined( __NetBSD__ ) || \
	defined( __OpenBSD__ ) || defined( __APPLE__ )
  /* Get BSD version macros.  This is less useful, or at least portable, 
     than it seems because the recommended 'BSD' macro is frozen in time in 
	 the 1990s, and so each BSD variant has defined its own replacement, or
	 in some cases several for good measures.  FreeBSD has 
	 '__FreeBSD_version' as a 7-digit decimal with the MSB being the major
	 version, NetBSD has 'NetBSD' but this is frozen in 1999, the current 
	 form is '__NetBSD_Version__' as an 8-digit decimal with the MSB being 
	 the major vesion, OpenBSD has 'OpenBSD' in the BSD-standard YYYYMM 
	 format, and Apple has a 'NeXTBSD' frozen in 1995 but otherwise only
	 '__APPLE_CC__' for the compiler version, otherwise all we have is
	 <TargetConditionals.h> to tell us whether we're building for OS X vs.
	 iOS (TARGET_OS_*) and the CPU type (TARGET_CPU_*) */
  #include <sys/param.h>
#endif /* *BSDs */
#include <signal.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/types.h>		/* Verschiedene komische Typen */
#include <sys/un.h>
#include <sys/wait.h>
/* #include <kitchensink.h> */

/* Crays and QNX 4.x don't have a rlimit/rusage so we have to fake the
   functions and structs */

#if defined( _CRAY ) || \
	( defined( __QNX__ ) && OSVERSION <= 4 )
  #define setrlimit( x, y )
  struct rlimit { int dummy1, dummy2; };
  struct rusage { int dummy; };
#endif /* Systems without rlimit/rusage */

/* If we're using threads, we have to protect the entropy gatherer with
   a mutex to prevent multiple threads from trying to initate polls at the
   same time.  Unlike the kernel mutexes, we don't have to worry about
   being called recursively, so there's no need for special-case handling
   for Posix' nasty non-reentrant mutexes */

#ifdef USE_THREADS
  #include <pthread.h>

  #define lockPollingMutex()	pthread_mutex_lock( &gathererMutex )
  #define unlockPollingMutex()	pthread_mutex_unlock( &gathererMutex )
#else
  #define lockPollingMutex()
  #define unlockPollingMutex()
#endif /* USE_THREADS */

/* The size of the intermediate buffer used to accumulate polled data,
   and an extra-large version for calls that return lots of data */

#define RANDOM_BUFSIZE			4096
#define BIG_RANDOM_BUFSIZE		( RANDOM_BUFSIZE * 2 )

#if BIG_RANDOM_BUFSIZE > MAX_INTLENGTH_SHORT
  #error RANDOM_BUFSIZE exceeds randomness accumulator size
#endif /* RANDOM_BUFSIZE > MAX_INTLENGTH_SHORT */

/* The structure containing information on random-data sources.  Each record 
   contains the source and a relative estimate of its usefulness (weighting) 
   which is used to scale the number of kB of output from the source (total 
   = data_bytes / usefulness).  Usually the weighting is in the range 1-3 
   (or 0 for especially useless sources), resulting in a usefulness rating 
   of 1...3 for each kB of source output (or 0 for the useless sources).

   If the source is constantly changing (certain types of network statistics
   have this characteristic) but the amount of output is small, the weighting
   is given as a negative value to indicate that the output should be treated
   as if a minimum of 1K of output had been obtained.  If the source produces
   a lot of output then the scale factor is fractional, resulting in a
   usefulness rating of < 1 for each kB of source output.

   In order to provide enough randomness to satisfy the requirements for a
   slow poll, we need to accumulate at least 20 points of usefulness (a
   typical system should get about 30 points).  This is useful not only for 
   use on source-starved systems but also in special circumstances like 
   running in a *BSD jail, in which only other processes running in the jail
   are visible, severely restricting the amount of entropy that can be 
   collected.

   Some potential options are missed out because of special considerations.
   pstat -i and pstat -f can produce amazing amounts of output (the record is
   600K on an Oracle server) that floods the buffer and doesn't yield
   anything useful (apart from perhaps increasing the entropy of the vmstat
   output a bit), so we don't bother with this.  pstat in general produces
   quite a bit of output, but it doesn't change much over time, so it gets
   very low weightings.  netstat -s produces constantly-changing output but
   also produces quite a bit of it, so it only gets a weighting of 2 rather
   than 3.  The same holds for netstat -in, which gets 1 rather than 2.  In
   addition some of the lower-ranked sources are either rather heavyweight
   or of low value, and frequently duplicate information obtained by other
   means like kstat or /procfs.  To avoid waiting for a long time for them
   to produce output, we only use them if earlier, quicker sources aren't
   available.

   Some binaries are stored in different locations on different systems so
   alternative paths are given for them.  The code sorts out which one to run
   by itself, once it finds an exectable somewhere it moves on to the next
   source.  The sources are arranged roughly in their order of usefulness,
   occasionally sources that provide a tiny amount of relatively useless
   data are placed ahead of ones that provide a large amount of possibly
   useful data because another 100 bytes can't hurt, and it means the buffer
   won't be swamped by one or two high-output sources. All the high-output
   sources are clustered towards the end of the list for this reason.  Some
   binaries are checked for in a certain order, for example under Slowaris
   /usr/ucb/ps understands aux as an arg, but the others don't.  Some systems
   have conditional defines enabling alternatives to commands that don't
   understand the usual options but will provide enough output (in the form
   of error messages) to look like they're the real thing, causing
   alternative options to be skipped (we can't check the return either
   because some commands return peculiar, non-zero status even when they're
   working correctly).

   In order to maximise use of the buffer, the code performs a form of run-
   length compression on its input where a repeated sequence of bytes is
   replaced by the occurrence count mod 256.  Some commands output an awful
   lot of whitespace, this measure greatly increases the amount of data that 
   we can fit in the buffer.

   When we scale the weighting using the SC() macro, some preprocessors may
   give a division by zero warning for the most obvious expression 'weight ?
   1024 / weight : 0' (and gcc 2.7.2.2 dies with a division by zero trap), so
   we define a value SC_0 that evaluates to zero when fed to '1024 / SC_0' */

#define SC( weight )	( int ) ( 1024 / weight )	/* Scale factor */
#define SC_0			16384				/* SC( SC_0 ) evalutes to 0 */

typedef struct {
	const char *path;		/* Path to check for existence of source */
	const char *arg;		/* Args for source */
	const int usefulness;	/* Usefulness of source */
	FILE *pipe;				/* Pipe to source as FILE * */
	int pipeFD;				/* Pipe to source as FD */
	pid_t pid;				/* pid of child for waitpid() */
	int length;				/* Quantity of output produced */
	const BOOLEAN hasAlternative;	/* Whether source has alt.location */
	} DATA_SOURCE_INFO;

static DATA_SOURCE_INFO dataSources[] = {
	/* Sources that are always polled */
	{ "/bin/vmstat", "-s", SC( -3 ), NULL, 0, 0, 0, TRUE },
	{ "/usr/bin/vmstat", "-s", SC( -3 ), NULL, 0, 0, 0, FALSE },
	{ "/bin/vmstat", "-c", SC( -3 ), NULL, 0, 0, 0, TRUE },
	{ "/usr/bin/vmstat", "-c", SC( -3 ), NULL, 0, 0, 0, FALSE },
#if defined( __APPLE__ )
	{ "/usr/bin/vm_stat", NULL, SC( -3 ), NULL, 0, 0, 0, FALSE },
#endif /* Mach version of vmstat */
	{ "/usr/bin/pfstat", NULL, SC( -2 ), NULL, 0, 0, 0, FALSE },
	{ "/bin/vmstat", "-i", SC( -2 ), NULL, 0, 0, 0, TRUE },
	{ "/usr/bin/vmstat", "-i", SC( -2 ), NULL, 0, 0, 0, FALSE },
#if defined( _AIX ) || defined( __SCO_VERSION__ )
	{ "/usr/bin/vmstat", "-f", SC( -1 ), NULL, 0, 0, 0, FALSE },
#endif /* OS-specific extensions to vmstat */
	{ "/usr/ucb/netstat", "-s", SC( 2 ), NULL, 0, 0, 0, TRUE },
	{ "/usr/bin/netstat", "-s", SC( 2 ), NULL, 0, 0, 0, TRUE },
	{ "/usr/sbin/netstat", "-s", SC( 2 ), NULL, 0, 0, 0, TRUE },
	{ "/bin/netstat", "-s", SC( 2 ), NULL, 0, 0, 0, TRUE },
	{ "/usr/etc/netstat", "-s", SC( 2 ), NULL, 0, 0, 0, FALSE },
	{ "/usr/bin/nfsstat", NULL, SC( 2 ), NULL, 0, 0, 0, FALSE },
	{ "/usr/ucb/netstat", "-m", SC( -1 ), NULL, 0, 0, 0, TRUE },
	{ "/usr/bin/netstat", "-m", SC( -1 ), NULL, 0, 0, 0, TRUE },
	{ "/usr/sbin/netstat", "-m", SC( -1 ), NULL, 0, 0, 0, TRUE },
	{ "/bin/netstat", "-m", SC( -1 ), NULL, 0, 0, 0, TRUE },
	{ "/usr/etc/netstat", "-m", SC( -1 ), NULL, 0, 0, 0, FALSE },
	{ "/usr/ucb/netstat", "-in", SC( -1 ), NULL, 0, 0, 0, TRUE },
	{ "/usr/bin/netstat", "-in", SC( -1 ), NULL, 0, 0, 0, TRUE },
	{ "/usr/sbin/netstat", "-in", SC( -1 ), NULL, 0, 0, 0, TRUE },
	{ "/bin/netstat", "-in", SC( -1 ), NULL, 0, 0, 0, TRUE },
	{ "/usr/etc/netstat", "-in", SC( -1 ), NULL, 0, 0, 0, FALSE },
#ifndef __SCO_VERSION__
	{ "/usr/sbin/snmp_request", "localhost public get 1.3.6.1.2.1.7.1.0", SC( -1 ), NULL, 0, 0, 0, FALSE }, /* UDP in */
	{ "/usr/sbin/snmp_request", "localhost public get 1.3.6.1.2.1.7.4.0", SC( -1 ), NULL, 0, 0, 0, FALSE }, /* UDP out */
	{ "/usr/sbin/snmp_request", "localhost public get 1.3.6.1.2.1.4.3.0", SC( -1 ), NULL, 0, 0, 0, FALSE }, /* IP ? */
	{ "/usr/sbin/snmp_request", "localhost public get 1.3.6.1.2.1.6.10.0", SC( -1 ), NULL, 0, 0, 0, FALSE }, /* TCP ? */
	{ "/usr/sbin/snmp_request", "localhost public get 1.3.6.1.2.1.6.11.0", SC( -1 ), NULL, 0, 0, 0, FALSE }, /* TCP ? */
	{ "/usr/sbin/snmp_request", "localhost public get 1.3.6.1.2.1.6.13.0", SC( -1 ), NULL, 0, 0, 0, FALSE }, /* TCP ? */
#else
	{ "/usr/sbin/snmpstat", "-an localhost public", SC( SC_0 ), NULL, 0, 0, 0, FALSE },
	{ "/usr/sbin/snmpstat", "-in localhost public", SC( SC_0 ), NULL, 0, 0, 0, FALSE }, /* Subset of netstat info */
	{ "/usr/sbin/snmpstat", "-Sn localhost public", SC( SC_0 ), NULL, 0, 0, 0, FALSE },
#endif /* SCO/UnixWare vs.everything else */
	{ "/usr/bin/smartctl", "-A /dev/hda" , SC( 1 ), NULL, 0, 0, 0, FALSE },
	{ "/usr/bin/smartctl", "-A /dev/hdb" , SC( 1 ), NULL, 0, 0, 0, FALSE },
	{ "/usr/bin/mpstat", NULL, SC( 1 ), NULL, 0, 0, 0, FALSE },
	{ "/usr/bin/w", NULL, SC( 1 ), NULL, 0, 0, 0, TRUE },
	{ "/usr/bsd/w", NULL, SC( 1 ), NULL, 0, 0, 0, FALSE },
	{ "/usr/bin/df", NULL, SC( 1 ), NULL, 0, 0, 0, TRUE },
	{ "/bin/df", NULL, SC( 1 ), NULL, 0, 0, 0, FALSE },
	{ "/usr/sbin/portstat", NULL, SC( 1 ), NULL, 0, 0, 0, FALSE },
	{ "/usr/bin/iostat", NULL, SC( SC_0 ), NULL, 0, 0, 0, FALSE },
	{ "/usr/bin/uptime", NULL, SC( SC_0 ), NULL, 0, 0, 0, TRUE },
	{ "/usr/bsd/uptime", NULL, SC( SC_0 ), NULL, 0, 0, 0, FALSE },
	{ "/usr/bin/vmstat", "-f", SC( SC_0 ), NULL, 0, 0, 0, TRUE },
	{ "/bin/vmstat", "-f", SC( SC_0 ), NULL, 0, 0, 0, TRUE },
	{ "/usr/ucb/netstat", "-n", SC( 0.5 ), NULL, 0, 0, 0, TRUE },
	{ "/usr/bin/netstat", "-n", SC( 0.5 ), NULL, 0, 0, 0, TRUE },
	{ "/usr/sbin/netstat", "-n", SC( 0.5 ), NULL, 0, 0, 0, TRUE },
	{ "/bin/netstat", "-n", SC( 0.5 ), NULL, 0, 0, 0, TRUE },
	{ "/usr/etc/netstat", "-n", SC( 0.5 ), NULL, 0, 0, 0, FALSE },

	/* End-of-lightweight-sources section marker */
	{ "", NULL, SC( SC_0 ), NULL, 0, 0, 0, FALSE },

	/* Potentially heavyweight or low-value sources that are only polled if
	   alternative sources aren't available.  ntptrace is somewhat
	   problematic in that some versions don't support -r and -t, made worse
	   by the fact that various servers in the commonly-used pool.ntp.org
	   cluster refuse to answer ntptrace.  As a result, using this can hang
	   for quite awhile before it times out, so we treat it as a heavyweight
	   source even though in theory it's a nice high-entropy lightweight
	   one */
	{ "/usr/sbin/ntptrace", "-r2 -t1 -nv", SC( -1 ), NULL, 0, 0, 0, FALSE },
#if defined( __sgi ) || defined( __hpux )
	{ "/bin/ps", "-el", SC( 0.3 ), NULL, 0, 0, 0, TRUE },
#endif /* SGI || PHUX */
	{ "/usr/ucb/ps", "aux", SC( 0.3 ), NULL, 0, 0, 0, TRUE },
	{ "/usr/bin/ps", "aux", SC( 0.3 ), NULL, 0, 0, 0, TRUE },
	{ "/bin/ps", "aux", SC( 0.3 ), NULL, 0, 0, 0, FALSE },
	{ "/usr/bin/ipcs", "-a", SC( 0.5 ), NULL, 0, 0, 0, TRUE },
	{ "/bin/ipcs", "-a", SC( 0.5 ), NULL, 0, 0, 0, FALSE },
							/* Unreliable source, depends on system usage */
	{ "/etc/pstat", "-p", SC( 0.5 ), NULL, 0, 0, 0, TRUE },
	{ "/bin/pstat", "-p", SC( 0.5 ), NULL, 0, 0, 0, FALSE },
	{ "/etc/pstat", "-S", SC( 0.2 ), NULL, 0, 0, 0, TRUE },
	{ "/bin/pstat", "-S", SC( 0.2 ), NULL, 0, 0, 0, FALSE },
	{ "/etc/pstat", "-v", SC( 0.2 ), NULL, 0, 0, 0, TRUE },
	{ "/bin/pstat", "-v", SC( 0.2 ), NULL, 0, 0, 0, FALSE },
	{ "/etc/pstat", "-x", SC( 0.2 ), NULL, 0, 0, 0, TRUE },
	{ "/bin/pstat", "-x", SC( 0.2 ), NULL, 0, 0, 0, FALSE },
	{ "/etc/pstat", "-t", SC( 0.1 ), NULL, 0, 0, 0, TRUE },
	{ "/bin/pstat", "-t", SC( 0.1 ), NULL, 0, 0, 0, FALSE },
							/* pstat is your friend */
#ifndef __SCO_VERSION__
	{ "/usr/sbin/sar", "-AR", SC( 0.05 ), NULL, 0, 0, 0, FALSE }, /* Only updated hourly */
#endif /* SCO/UnixWare */
	{ "/usr/bin/last", "-n 50", SC( 0.3 ), NULL, 0, 0, 0, TRUE },
#ifdef __sgi
	{ "/usr/bsd/last", "-50", SC( 0.3 ), NULL, 0, 0, 0, FALSE },
#endif /* SGI */
#ifdef __hpux
	{ "/etc/last", "-50", SC( 0.3 ), NULL, 0, 0, 0, FALSE },
#endif /* PHUX */
	{ "/usr/bsd/last", "-n 50", SC( 0.3 ), NULL, 0, 0, 0, FALSE },
#ifdef sun
	{ "/usr/bin/showrev", "-a", SC( 0.1 ), NULL, 0, 0, 0, FALSE },
	{ "/usr/sbin/swap", "-l", SC( SC_0 ), NULL, 0, 0, 0, FALSE },
	{ "/usr/sbin/prtconf", "-v", SC( SC_0 ), NULL, 0, 0, 0, FALSE },
#endif /* SunOS/Slowaris */
	{ "/usr/sbin/psrinfo", NULL, SC( SC_0 ), NULL, 0, 0, 0, FALSE },
	{ "/usr/bin/lsof", "-blnwP", SC( 0.3 ), NULL, 0, 0, 0, TRUE },
	{ "/usr/local/bin/lsof", "-blnwP", SC( 0.3 ), NULL, 0, 0, 0, FALSE },
							/* Output is very system and version-dependent
							   and can also be extremely voluminous */
	{ "/usr/sbin/snmp_request", "localhost public get 1.3.6.1.2.1.5.1.0", SC( 0.1 ), NULL, 0, 0, 0, FALSE }, /* ICMP ? */
	{ "/usr/sbin/snmp_request", "localhost public get 1.3.6.1.2.1.5.3.0", SC( 0.1 ), NULL, 0, 0, 0, FALSE }, /* ICMP ? */
	{ "/etc/arp", "-a", SC( 0.1 ), NULL, 0, 0, 0, TRUE },
	{ "/usr/etc/arp", "-a", SC( 0.1 ), NULL, 0, 0, 0, TRUE },
	{ "/usr/bin/arp", "-a", SC( 0.1 ), NULL, 0, 0, 0, TRUE },
	{ "/usr/sbin/arp", "-a", SC( 0.1 ), NULL, 0, 0, 0, FALSE },
	{ "/usr/sbin/ripquery", "-nw 1 127.0.0.1", SC( 0.1 ), NULL, 0, 0, 0, FALSE },
	{ "/bin/lpstat", "-t", SC( 0.1 ), NULL, 0, 0, 0, TRUE },
	{ "/usr/bin/lpstat", "-t", SC( 0.1 ), NULL, 0, 0, 0, TRUE },
	{ "/usr/ucb/lpstat", "-t", SC( 0.1 ), NULL, 0, 0, 0, FALSE },
	{ "/usr/bin/tcpdump", "-c 5 -efvvx", SC( 1 ), NULL, 0, 0, 0, FALSE },
							/* This is very environment-dependant.  If
							   network traffic is low, it'll probably time
							   out before delivering 5 packets, which is OK
							   because it'll probably be fixed stuff like ARP
							   anyway */
	{ "/usr/sbin/advfsstat", "-b usr_domain", SC( SC_0 ), NULL, 0, 0, 0, FALSE },
	{ "/usr/sbin/advfsstat", "-l 2 usr_domain", SC( 0.5 ), NULL, 0, 0, 0, FALSE },
	{ "/usr/sbin/advfsstat", "-p usr_domain", SC( SC_0 ), NULL, 0, 0, 0, FALSE },
							/* This is a complex and screwball program.  Some
							   systems have things like rX_dmn, x = integer,
							   for RAID systems, but the statistics are
							   pretty dodgy */
#if 0
	/* The following aren't enabled since they're somewhat slow and not very
	   unpredictable, however they give an indication of the sort of sources
	   you can use (for example the finger might be more useful on a
	   firewalled internal network) */
	{ "/usr/bin/finger", "@ml.media.mit.edu", SC( 0.9 ), NULL, 0, 0, 0, FALSE },
	{ "/usr/local/bin/wget", "-O - http://lavarand.sgi.com/block.html", SC( 0.9 ), NULL, 0, 0, 0, FALSE },
	{ "/bin/cat", "/usr/spool/mqueue/syslog", SC( 0.9 ), NULL, 0, 0, 0, FALSE },
#endif /* 0 */

	/* End-of-sources marker */
	{ NULL, NULL, 0, NULL, 0, 0, 0, FALSE }, 
		{ NULL, NULL, 0, NULL, 0, 0, 0, FALSE }
	};

/* Variables to manage the child process that fills the buffer */

static pid_t gathererProcess = 0;/* The child process that fills the buffer */
static BYTE *gathererBuffer;	/* Shared buffer for gathering random noise */
static int gathererMemID;		/* ID for shared memory */
static int gathererBufSize;		/* Size of the shared memory buffer */
static struct sigaction gathererOldHandler;	/* Previous signal handler */
#ifdef USE_THREADS
  static pthread_mutex_t gathererMutex;	/* Mutex to protect the polling */
#endif /* USE_THREADS */

/* The struct at the start of the shared memory buffer used to communicate
   information from the child to the parent */

typedef struct {
	int usefulness;				/* Usefulness of data in buffer */
	int noBytes;				/* No.of bytes in buffer */
	} GATHERER_INFO;

/****************************************************************************
*																			*
*								Utility Functions							*
*																			*
****************************************************************************/

#if defined( __hpux ) && ( OSVERSION == 9 )

/* PHUX 9.x doesn't support getrusage in libc (wonderful...) */

#include <syscall.h>

CHECK_RETVAL STDC_NONNULL_ARG( ( 2 ) ) \
static int getrusage( int who, OUT struct rusage *rusage )
	{
	return( syscall( SYS_getrusage, who, rusage ) );
	}
#endif /* __hpux */

/****************************************************************************
*																			*
*									Fast Poll								*
*																			*
****************************************************************************/

/* Fast poll - not terribly useful.  SCO has a gettimeofday() prototype but
   no actual system call that implements it, and no getrusage() at all, so
   we use times() instead */

#if defined( _CRAY ) || defined( _M_XENIX )
  #include <sys/times.h>
#endif /* Systems without getrusage() */

void fastPoll( void )
	{
	RANDOM_STATE randomState;
	BYTE buffer[ RANDOM_BUFSIZE + 8 ];
#if !( defined( _CRAY ) || defined( _M_XENIX ) )
	struct timeval tv;
  #if !( defined( __QNX__ ) && OSVERSION <= 4 )
	struct rusage rusage;
  #endif /* !QNX 4.x */
#else
	struct tms tms;
#endif /* Systems without getrusage() */
#ifdef _AIX
	timebasestruct_t cpuClockInfo;
#endif /* Aches */
#if ( defined( sun ) && ( OSVERSION >= 5 ) )
	hrtime_t hrTime;
#endif /* Slowaris */
#if ( defined( __QNX__ ) && OSVERSION >= 5 )
	uint64_t clockCycles;
#endif /* QNX */
#if defined( _POSIX_TIMERS ) && ( _POSIX_TIMERS > 0 ) && 0	/* See below */
	struct timespec timeSpec;
#endif /* _POSIX_TIMERS > 0 */
	int status;

	status = initRandomData( randomState, buffer, RANDOM_BUFSIZE );
	ENSURES_V( cryptStatusOK( status ) );

	/* Mix in the process ID.  This doesn't change per process but will
	   change if the process forks, ensuring that the parent and child data
	   differs from the parent */
	addRandomValue( randomState, getpid() );

#if !( defined( _CRAY ) || defined( _M_XENIX ) )
	gettimeofday( &tv, NULL );
	addRandomValue( randomState, tv.tv_sec );
	addRandomValue( randomState, tv.tv_usec );

	/* SunOS 5.4 has the function call but no prototypes for it, if you're
	   compiling this under 5.4 you'll have to copy the header files from 5.5
	   or something similar */
  #if !( defined( __QNX__ ) && OSVERSION <= 4 )
	getrusage( RUSAGE_SELF, &rusage );
	addRandomData( randomState, &rusage, sizeof( struct rusage ) );
  #endif /* !QNX 4.x */
#else
	/* Merely a subset of getrusage(), but it's the best that we can do.  On
	   Crays it provides access to the hardware clock, so the data is quite
	   good */
	times( &tms );
	addRandomData( randomState, &tms, sizeof( struct tms ) );
#endif /* Systems without getrusage() */
#ifdef _AIX
	/* Add the value of the nanosecond-level CPU clock or time base register */
	read_real_time( &cpuClockInfo, sizeof( timebasestruct_t ) );
	addRandomData( randomState, &cpuClockInfo, sizeof( timebasestruct_t ) );
#endif /* _AIX */
#if ( defined( sun ) && ( OSVERSION >= 5 ) )
	/* Read the Sparc %tick register (equivalent to the P5 TSC).  This is
	   only readable by the kernel by default, although Solaris 8 and newer
	   make it readable in user-space.  To do this portably, we use
	   gethrtime(), which does the same thing */
	hrTime = gethrtime();
	addRandomData( randomState, &hrTime, sizeof( hrtime_t ) );
#endif /* Slowaris */
#ifdef rdtscl
	if( getSysCaps() & SYSCAP_FLAG_RDTSC )
		{
		unsigned long tscValue;

		rdtscl( tscValue );
		addRandomValue( randomState, tscValue );
		}
#endif /* rdtsc available */
#if ( defined( __QNX__ ) && OSVERSION >= 5 )
	/* Return the output of RDTSC or its equivalent on other systems.  We
	   don't worry about locking the thread to a CPU since we're not using
	   it for timing (in fact being run on another CPU helps the entropy) */
	clockCycles = ClockCycles();
	addRandomData( randomState, &clockCycles, sizeof( uint64_t ) );
#endif /* QNX */
	/* Get real-time (or as close to it as possible) clock information if 
	   it's available.  These values are platform-specific, but typically use 
	   a high-resolution source like the Pentium TSC.
	   
	   (Unfortunately we can't safely use this function because it's often 
	   not present in libc but needs to be pulled in via the real-time 
	   extensions library librt instead, which causes all sorts of 
	   portability problems) */
#if defined( _POSIX_TIMERS ) && ( _POSIX_TIMERS > 0 ) && 0
	if( clock_gettime( CLOCK_REALTIME, &timeSpec ) == 0 )
		addRandomData( randomState, &timeSpec, sizeof( struct timespec ) );
	if( clock_gettime( CLOCK_PROCESS_CPUTIME_ID, &timeSpec ) == 0 )
		addRandomData( randomState, &timeSpec, sizeof( struct timespec ) );
	if( clock_gettime( CLOCK_THREAD_CPUTIME_ID, &timeSpec ) == 0 )
		addRandomData( randomState, &timeSpec, sizeof( struct timespec ) );
#endif /* _POSIX_TIMERS > 0 */

	/* Flush any remaining data through */
	endRandomData( randomState, 0 );
	}

/****************************************************************************
*																			*
*								Slow Poll Sources							*
*																			*
****************************************************************************/

/* *BSD-specific poll using sysctl */

#if defined( __FreeBSD__ ) || defined( __NetBSD__ ) || \
	defined( __OpenBSD__ ) || defined( __APPLE__ )

#define USE_SYSCTL
#include <sys/sysctl.h>
#include <net/route.h>				/* For CTL_NET:AF_ROUTE:0:AF_INET:\
									   NET_RT_FLAGS idents */
#include <netinet/in.h>				/* For CTL_NET identifiers */
#include <sys/gmon.h>				/* For CTL_KERN:KERN_PROF identifiers */
#if defined( __NetBSD__ )
  #include <uvm/uvm_param.h>		/* For CTL_VM identifiers */
#else
  #include <vm/vm_param.h>			/* For CTL_VM identifiers */
#endif /* BSD-variant-specific include paths */

typedef struct {
	const int mibCount;				/* Number of MIB entries */
	const int mib[ 6 ];				/* MIB values for this info */
	const int quality;				/* Entropy quality if present */
	} SYSCTL_INFO;

static const SYSCTL_INFO sysctlInfo[] = {
	/* Hardware info */
	{ 2, { CTL_HW, HW_MACHINE } },	/* Machine class */
	{ 2, { CTL_HW, HW_MACHINE_ARCH } }, /* Machine architecture */
	{ 2, { CTL_HW, HW_MODEL } },	/* Machine model */
#ifdef HW_IOSTATS
	{ 2, { CTL_HW, HW_IOSTATS } },	/* struct io_sysctl for each device 
									   containing microsecond times and byte 
									   counts */
#endif /* HW_IOSTATS */
	{ 2, { CTL_HW, HW_PHYSMEM } },	/* Physical memory */
#ifdef HW_REALMEM
	{ 2, { CTL_HW, HW_REALMEM } },	/* Real memory */
#endif /* HW_REALMEM */
	{ 2, { CTL_HW, HW_USERMEM } },	/* Non-kernel memory */

	/* Kernel info */
	{ 2, { CTL_KERN, KERN_BOOTTIME }, 1 }, 
									/* Time system was booted */
	{ 2, { CTL_KERN, KERN_CLOCKRATE } },
									/* struct clockinfo of clock frequecies */
#ifdef KERN_CP_TIME
	{ 2, { CTL_KERN, KERN_CP_TIME }, 1 },
									/* Number of clock ticks in different CPU
									   states */
#endif /* KERN_CP_TIME */
#ifdef KERN_DRIVERS
	{ 2, { CTL_KERN, KERN_DRIVERS } },/* struct kinfo_drivers with major/minor
									   ID and name for all drivers */
#endif /* KERN_DRIVERS */
#ifdef KERN_EVCNT
	{ 2, { CTL_KERN, KERN_EVCNT } },/* struct evcnts for all active event 
									   counters.  There usually won't be any
									   set so this won't produce a result from
									   sysctl() */
#endif /* KERN_EVCNT */
	{ 2, { CTL_KERN, KERN_FILE }, 5 }, 
									/* struct xfile for each file in the system, 
									   containing process IDs, fd no., ref.count, 
									   file offset, vnode, and flags.  Produces a
									   huge amount of output so typically gets
									   truncated at SYSCTL_BUFFER_SIZE */
#ifdef KERN_HARDCLOCK_TICKS
	{ 2, { CTL_KERN, KERN_HARDCLOCK_TICKS } },
									/* Number of hardclock (hard real-time timer) 
									   ticks */
#endif /* KERN_HARDCLOCK_TICKS */
	{ 2, { CTL_KERN, KERN_HOSTID } }, /* Host ID */
	{ 2, { CTL_KERN, KERN_HOSTNAME } },	/* Hostname */
#ifdef KERN_HOSTUUID
	{ 2, { CTL_KERN, KERN_HOSTUUID } },	/* Host UUID */
#endif /* KERN_HOSTUUID */
#ifdef KERN_NTPTIME
	{ 2, { CTL_KERN, KERN_NTPTIME }, 1 },
									/* struct ntptimeval with NTP accuracy
									   information */
	{ 2, { CTL_KERN, KERN_TIMEX }, 3 }, 
									/* struct timex containing detailed NTP
									   statistics.  This is a useful source
									   but typically isn't available so won't 
									   produce a result from sysctl() */
#endif /* KERN_NTPTIME */
#ifdef KERN_OSRELDATE
	{ 2, { CTL_KERN, KERN_OSRELDATE } }, /* OS release version */
#endif /* KERN_OSRELDATE */
	{ 2, { CTL_KERN, KERN_OSRELEASE } }, /* OS release string */
	{ 2, { CTL_KERN, KERN_OSREV } }, /* System revision string */
	{ 2, { CTL_KERN, KERN_OSTYPE } }, /* System type string */
	{ 3, { CTL_KERN, KERN_PROC, KERN_PROC_ALL }, 20, }, 
									/* struct kinfo_proc for each process 
									   containing a struct proc and a struct 
									   eproc which contain everything you 
									   could want to know about a process,
									   see /sys/sys/proc.h and 
									   /sys/sys/kinfo_proc.h.  Produces a
									   huge amount of output so typically 
									   gets truncated at SYSCTL_BUFFER_SIZE */
#ifdef KERN_PROC2
	{ 6, { CTL_KERN, KERN_PROC2, KERN_PROC_ALL, 0, sizeof( struct kinfo_proc2 ), 20 }, 10, }, 
									/* struct kinfo_proc2 containing a 
									   superset of struct kinfo_proc.  We 
									   give this a lower weight than it 
									   actually contains because a of the 
									   contents have already been obtained
									   via KERN_PROC.  Produces a huge 
									   amount of output so typically gets
									   truncated at SYSCTL_BUFFER_SIZE */
#endif /* KERN_PROC2 */
	{ 3, { CTL_KERN, KERN_PROF, GPROF_COUNT }, 10 },
									/* If kernel is compiled for profiling, 
									   an array of statistical program 
									   counter counts.  This typically isn't
									   enabled so won't produce a result from
									   sysctl() */
#ifdef KERN_TKSTAT
	{ 3, { CTL_KERN, KERN_TKSTAT, KERN_TKSTAT_CANCC } },
	{ 3, { CTL_KERN, KERN_TKSTAT, KERN_TKSTAT_NIN } },
	{ 3, { CTL_KERN, KERN_TKSTAT, KERN_TKSTAT_NOUT } },
	{ 3, { CTL_KERN, KERN_TKSTAT, KERN_TKSTAT_RAWCC } },
									/* Terminal chars sent/received */
#endif /* KERN_TKSTAT */
	{ 2, { CTL_KERN, KERN_VERSION } }, /* System version string  */
	{ 2, { CTL_KERN, KERN_VNODE }, 15 }, 
									/* struct xvnode for each vnode, see 
									   /sys/sys/vnode.h.  Produces a huge 
									   amount of output so typically gets
									   truncated at SYSCTL_BUFFER_SIZE */

	/* Networking info */
	{ 6, { CTL_NET, AF_ROUTE, 0, AF_INET, NET_RT_DUMP, 0 }, 5 },
									/* IPv4 routing table */
	{ 6, { CTL_NET, AF_ROUTE, 0, AF_INET6, NET_RT_DUMP, 0 }, 5 },
									/* IPv6 routing table */
	{ 6, { CTL_NET, AF_ROUTE, 0, AF_INET, NET_RT_FLAGS, RTF_LLINFO }, 5 },
									/* ARP cache */

	/* VM info */
#ifdef VM_LOADAVG 
	{ 2, { CTL_VM, VM_LOADAVG } },	/* Load average */
#endif /* VM_LOADAVG */
#ifdef VM_TOTAL
	{ 2, { CTL_VM, VM_TOTAL }, 5 },	/* struct vmtotal with count of jobs in
									   various states and amounts of virtual
									   memory */
#endif /* VM_TOTAL */
#ifdef VM_UVMEXP
	{ 2, { CTL_VM, VM_UVMEXP }, 10 },	
									/* struct uvmexp containing global state 
									   of the UVM system */
#endif /* VM_UVMEXP */
	{ 0, { 0 } }, { 0, { 0 } }
	};

#define SYSCTL_BUFFER_SIZE			16384

CHECK_RETVAL \
static int getSysctlData( void )
	{
	RANDOM_STATE randomState;
	BYTE buffer[ BIG_RANDOM_BUFSIZE + 8 ];
	BYTE sysctlBuffer[ SYSCTL_BUFFER_SIZE + 8 ];
	int quality = 0, i;

	initRandomData( randomState, buffer, BIG_RANDOM_BUFSIZE );

	/* Get each set of sysctl() information.  Since some of the information 
	   returned can be rather lengthy, we optionally send it directly to the 
	   randomness pool rather than using the accumulator */
	for( i = 0; sysctlInfo[ i ].mibCount != 0; i++ )
		{
		size_t size = SYSCTL_BUFFER_SIZE;
		int status;

		/* Since we only care about the information that's returned as an 
		   entropy source, we treat a buffer-not-large-enough error (errno
		   = ENOMEM) as an OK status for the purpose of providing entropy.  
		   Since ENOMEM can be returned for reasons other than the buffer 
		   not being large enough, we sanity-check the result by requiring
		   that at least half the buffer was filled with information */
 		status = sysctl( sysctlInfo[ i ].mib, sysctlInfo[ i ].mibCount, 
						 sysctlBuffer, &size, NULL, 0 );
		if( status == -1 && errno == ENOMEM )
			{
#ifdef DEBUG_RANDOM
			printf( __FILE__ ": Overflow in sysctl %d:%d, using %d bytes.\n", 
					sysctlInfo[ i ].mib[ 0 ], sysctlInfo[ i ].mib[ 1 ], 
					size );
#endif /* DEBUG_RANDOM */
			if( size >= SYSCTL_BUFFER_SIZE / 2 )
				status = 0;
			}
		if( status )
			{
#ifdef DEBUG_RANDOM
			printf( __FILE__ ": Skipped sysctl %d:%d due to error status.\n", 
					sysctlInfo[ i ].mib[ 0 ], sysctlInfo[ i ].mib[ 1 ] );
#endif /* DEBUG_RANDOM */
			continue;
			}
#ifdef DEBUG_RANDOM
		printf( __FILE__ ": Got %d bytes data from sysctl %d:%d.\n", 
				size, sysctlInfo[ i ].mib[ 0 ], sysctlInfo[ i ].mib[ 1 ] );
#endif /* DEBUG_RANDOM */

		/* We got some data, add it to the entropy pool */
		if( size > BIG_RANDOM_BUFSIZE )
			{
			MESSAGE_DATA msgData;

			setMessageData( &msgData, sysctlBuffer, size );
			krnlSendMessage( SYSTEM_OBJECT_HANDLE, IMESSAGE_SETATTRIBUTE_S,
							 &msgData, CRYPT_IATTRIBUTE_ENTROPY );
			}
		else
			addRandomData( randomState, sysctlBuffer, size );
		quality += sysctlInfo[ i ].quality;
		}
#ifdef DEBUG_RANDOM
	printf( __FILE__ ": BSD sysctl contributed %d value.\n", quality );
#endif /* DEBUG_RANDOM */

	/* Flush any remaining data through and provide an estimate of its
	   value.  We cap it at 80 to ensure that some data is still coming 
	   from other sources */
	if( quality > 80 )
		quality = 80;
	endRandomData( randomState, quality );

	return( quality );
	}
#endif /* *BSDs */

/* Slowaris-specific slow poll using kstat, which provides kernel statistics.
   Since there can be a hundred or more of these, we use a larger-than-usual
   intermediate buffer to cut down on kernel traffic.
   
   Unfortunately Slowaris is the only OS that provides this interface, some
   of the *BSDs have kenv, but this just returns fixed information like PCI
   bus device addresses and so on, and isn't useful for providing entropy */

#if ( defined( sun ) && ( OSVERSION >= 5 ) )

#define USE_KSTAT
#include <kstat.h>

CHECK_RETVAL \
static int getKstatData( void )
	{
	kstat_ctl_t *kc;
	kstat_t *ksp;
	RANDOM_STATE randomState;
	BYTE buffer[ BIG_RANDOM_BUFSIZE + 8 ];
	int noEntries = 0, quality;

	/* Try and open a kernel stats handle */
	if( ( kc = kstat_open() ) == NULL )
		return( 0 );

	initRandomData( randomState, buffer, BIG_RANDOM_BUFSIZE );

	/* Walk down the chain of stats reading each one.  Since some of the
	   stats can be rather lengthy, we optionally send them directly to
	   the randomness pool rather than using the accumulator */
	for( ksp = kc->kc_chain; ksp != NULL; ksp = ksp->ks_next )
		{
		if( kstat_read( kc, ksp, NULL ) == -1 || \
			ksp->ks_data_size <= 0 )
			continue;
		addRandomData( randomState, ksp, sizeof( kstat_t ) );
		if( ksp->ks_data_size > BIG_RANDOM_BUFSIZE )
			{
			MESSAGE_DATA msgData;

			setMessageData( &msgData, ksp->ks_data, ksp->ks_data_size );
			krnlSendMessage( SYSTEM_OBJECT_HANDLE, IMESSAGE_SETATTRIBUTE_S,
							 &msgData, CRYPT_IATTRIBUTE_ENTROPY );
			}
		else
			addRandomData( randomState, ksp->ks_data, ksp->ks_data_size );
		noEntries++;
		}
	kstat_close( kc );
#ifdef DEBUG_RANDOM
	printf( __FILE__ ": Solaris kstats contributed %d entries.\n", 
			noEntries );
#endif /* DEBUG_RANDOM */

	/* Flush any remaining data through and produce an estimate of its
	   value.  We require that we get at least 50 entries and give them a
	   maximum value of 35 to ensure that some data is still coming from
	   other sources */
	quality = ( noEntries > 50 ) ? 35 : 0;
	endRandomData( randomState, quality );

	return( quality );
	}
#endif /* Slowaris */

/* SYSV /proc interface, which provides assorted information that usually
   has to be obtained the hard way via a slow poll.

   Note that getProcData() gets data from the legacy /proc pseudo-filesystem
   using ioctls() whereas getProcFSdata()gets data from the current /procfs
   filesystem using file reads */

#if ( defined( sun ) && ( OSVERSION >= 5 ) ) || defined( __osf__ ) || \
	  defined( __alpha__ ) || \
	  ( defined( __linux__ ) && !defined( __Android__ ) )

#define USE_PROC
#include <sys/procfs.h>

CHECK_RETVAL \
static int getProcData( void )
	{
#ifdef PIOCSTATUS
	prstatus_t prStatus;
#endif /* PIOCSTATUS */
#ifdef PIOCPSINFO
	prpsinfo_t prMisc;
#endif /* PIOCPSINFO */
#ifdef PIOCUSAGE
	prusage_t prUsage;
#endif /* PIOCUSAGE */
#ifdef PIOCACINFO
	struct pracinfo pracInfo;
#endif /* PIOCACINFO */
	RANDOM_STATE randomState;
	BYTE buffer[ RANDOM_BUFSIZE + 8 ];
	char fileName[ 128 + 8 ];
	int fd, noEntries = 0, quality, status;

	/* Try and open the process info for this process.  We don't use 
	   O_NOFOLLOW because on some Unixen special files can be symlinks and 
	   in any case a system that allows attackers to mess with privileged 
	   filesystems like this is presumably a goner anyway */
	sprintf_s( fileName, 128, "/proc/%d", getpid() );
	if( ( fd = open( fileName, O_RDONLY ) ) == -1 )
		return( 0 );
	if( fd <= 2 )
		{
		/* We've been given a standard I/O handle, something's wrong */
		close( fd );
		return( 0 );
		}

	status = initRandomData( randomState, buffer, RANDOM_BUFSIZE );
	ENSURES_EXT( cryptStatusOK( status ), 0 );

	/* Get the process status information, misc information, and resource
	   usage */
#ifdef PIOCSTATUS
	if( ioctl( fd, PIOCSTATUS, &prStatus ) != -1 )
		{
#ifdef DEBUG_RANDOM
		printf( __FILE__ ": PIOCSTATUS contributed %d bytes.\n",
				sizeof( prstatus_t ) );
#endif /* DEBUG_RANDOM */
		addRandomData( randomState, &prStatus, sizeof( prstatus_t ) );
		noEntries++;
		}
#endif /* PIOCSTATUS */
#ifdef PIOCPSINFO
	if( ioctl( fd, PIOCPSINFO, &prMisc ) != -1 )
		{
#ifdef DEBUG_RANDOM
		printf( __FILE__ ": PIOCPSINFO contributed %d bytes.\n",
				sizeof( prpsinfo_t ) );
#endif /* DEBUG_RANDOM */
		addRandomData( randomState, &prMisc, sizeof( prpsinfo_t ) );
		noEntries++;
		}
#endif /* PIOCPSINFO */
#ifdef PIOCUSAGE
	if( ioctl( fd, PIOCUSAGE, &prUsage ) != -1 )
		{
#ifdef DEBUG_RANDOM
		printf( __FILE__ ": PIOCUSAGE contributed %d bytes.\n",
				sizeof( prusage_t ) );
#endif /* DEBUG_RANDOM */
		addRandomData( randomState, &prUsage, sizeof( prusage_t ) );
		noEntries++;
		}
#endif /* PIOCUSAGE */

#ifdef PIOCACINFO
	if( ioctl( fd, PIOCACINFO, &pracInfo ) != -1 )
		{
#ifdef DEBUG_RANDOM
		printf( __FILE__ ": PIOCACINFO contributed %d bytes.\n",
				sizeof( struct pracinfo ) );
#endif /* DEBUG_RANDOM */
		addRandomData( randomState, &pracInfo, sizeof( struct pracinfo ) );
		noEntries++;
		}
#endif /* PIOCACINFO */
	close( fd );

	/* Flush any remaining data through and produce an estimate of its
	   value.  We require that at least two of the sources exist and accesses
	   to them succeed, and give them a relatively low value since they're
	   returning information that has some overlap with that returned by the
	   general slow poll (although there's also a lot of low-level stuff
	   present that the slow poll doesn't get) */
	quality = ( noEntries > 2 ) ? 10 : 0;
	endRandomData( randomState, quality );

	return( quality );
	}
#endif /* Slowaris || OSF/1 || Linux */

#ifdef __iOS__ 

CHECK_RETVAL \
static int getIOSData( void )
	{
	RANDOM_STATE randomState;
	BYTE buffer[ RANDOM_BUFSIZE + 8 ];
	int quality = 0, status;

	/* Get the random data from the iOS system randomness routine.  Although 
	   SecRandomCopyBytes() takes as its first parameter the generator type, 
	   only one is allowed, kSecRandomDefault, after which the call is 
	   passed down to CCRandomCopyBytes(), which does something with one of 
	   the NIST DRBGs, but it's all obfuscated with macros and function 
	   pointers so it's hard to tell what.

	   Initially SecRandomCopyBytes() was just a wrapper for a thread-safe
	   read of Apple's /dev/random (for which see the comment in 
	   getDevRandomData() about the value of this and why we only assign a 
	   quality factor of 60%), however what's in use now isn't a /dev/random
	   read any more but something much more complex (see above).
	   
	   Another possible complication is that if both SecRandomCopyBytes() 
	   and the explicit /dev/random read that we perform ourselves are 
	   getting their input from the same source then we should only count 
	   its value once, however the Apple current code, which seems to be out 
	   of sync with the documentation, appears to do more than that */
	status = initRandomData( randomState, buffer, RANDOM_BUFSIZE );
	ENSURES_EXT( cryptStatusOK( status ), 0 );
	status = SecRandomCopyBytes( kSecRandomDefault, RANDOM_BUFSIZE, buffer );
	if( status == 0 )
		{
#ifdef DEBUG_RANDOM
		printf( __FILE__ ": SecRandomCopyBytes contributed %d bytes.\n",
				RANDOM_BUFSIZE );
#endif /* DEBUG_RANDOM */
		addRandomData( randomState, buffer, RANDOM_BUFSIZE );
		quality = 60;
		}
	endRandomData( randomState, quality );

	return( quality );
	}
#endif /* __iOS__  */

/* Named process information /procfs interface.  Each source is given a 
   weighting of 1-3, with 1 being a static (although unpredictable) source,
   2 being a slowly-changing source, and 3 being a rapidly-changing
   source */

CHECK_RETVAL \
static int getProcFSdata( void )
	{
	typedef struct {
		const char *source;
		const int value;
		} PROCSOURCE_INFO;
	static const PROCSOURCE_INFO procSources[] = {
		{ "/proc/diskstats", 2 }, { "/proc/interrupts", 3 },
		{ "/proc/loadavg", 2 }, { "/proc/locks", 1 },
		{ "/proc/meminfo", 3 }, { "/proc/net/dev", 2 },
		{ "/proc/net/ipx", 2 }, { "/proc/modules", 1 },
		{ "/proc/mounts", 1 }, { "/proc/net/netstat", 2 },
		{ "/proc/net/rt_cache", 1 }, { "/proc/net/rt_cache_stat", 3 },
		{ "/proc/net/snmp", 2 }, { "/proc/net/softnet_stat", 2 },
		{ "/proc/net/stat/arp_cache", 3 }, { "/proc/net/stat/ndisc_cache", 2 },
		{ "/proc/net/stat/rt_cache", 3 }, { "/proc/net/tcp", 3 },
		{ "/proc/net/udp", 2 }, { "/proc/net/wireless", 2 },
		{ "/proc/slabinfo", 3 }, { "/proc/stat", 3 },
		{ "/proc/sys/fs/inode-state", 1 }, { "/proc/sys/fs/file-nr", 1 },
		{ "/proc/sys/fs/dentry-state", 1 }, { "/proc/sysvipc/msg", 1 },
		{ "/proc/sysvipc/sem", 1 }, { "/proc/sysvipc/shm", 1 },
		{ "/proc/zoneinfo", 3 },
		{ "/sys/devices/system/node/node0/numastat", 2 },
		{ NULL, 0 }, { NULL, 0 }
		};
	MESSAGE_DATA msgData;
	BYTE buffer[ 1024 + 8 ];
	int procIndex, procFD, procValue = 0, quality;

	/* Read the first 1K of data from some of the more useful sources (most
	   of these produce far less than 1K output) */
	for( procIndex = 0; 
		 procSources[ procIndex ].source != NULL && \
			procIndex < FAILSAFE_ARRAYSIZE( procSources, PROCSOURCE_INFO );
		 procIndex++ )
		{
		int count, status;

		/* Try and open the data source.  We don't use O_NOFOLLOW because on 
		   some Unixen special files can be symlinks and in any case a 
		   system that allows attackers to mess with privileged filesystems 
		   like this is presumably a goner anyway */
		procFD = open( procSources[ procIndex ].source, O_RDONLY );
		if( procFD < 0 )
			continue;
		if( procFD <= 2 )
			{
			/* We've been given a standard I/O handle, something's wrong */
			close( procFD );
			return( 0 );
			}

		/* Read data from the source */
		count = read( procFD, buffer, 1024 );
		if( count > 16 )
			{
#ifdef DEBUG_RANDOM
			printf( __FILE__ ": %s contributed %d bytes.\n",
					procSources[ procIndex ].source, count );
#endif /* DEBUG_RANDOM */
			setMessageData( &msgData, buffer, count );
			status = krnlSendMessage( SYSTEM_OBJECT_HANDLE, 
									  IMESSAGE_SETATTRIBUTE_S, &msgData,
									  CRYPT_IATTRIBUTE_ENTROPY );
			if( cryptStatusOK( status ) )
				procValue += procSources[ procIndex ].value;
			}
		close( procFD );
		}
	ENSURES( procIndex < FAILSAFE_ARRAYSIZE( procSources, PROCSOURCE_INFO ) );
	zeroise( buffer, 1024 );
	if( procValue < 5 )
		return( 0 );

	/* Produce an estimate of the data's value.  We require that we get a
	   quality value of at least 5 and limit it to a maximum value of 50 to 
	   ensure that some data is still coming from other sources */
	quality = min( procValue, 50 );
	krnlSendMessage( SYSTEM_OBJECT_HANDLE, IMESSAGE_SETATTRIBUTE,
					 ( MESSAGE_CAST ) &quality, 
					 CRYPT_IATTRIBUTE_ENTROPY_QUALITY );
	return( quality );
	}

/* /dev/random interface */

#define DEVRANDOM_BYTES		128

CHECK_RETVAL \
static int getDevRandomData( void )
	{
	MESSAGE_DATA msgData;
	BYTE buffer[ DEVRANDOM_BYTES + 8 ];
#if defined( __APPLE__ ) || ( defined( __FreeBSD__ ) && OSVERSION >= 5 )
	static const int quality = 60;	/* See comment below */
#else
	static const int quality = 80;
#endif /* Mac OS X || FreeBSD 5.x */
	int randFD, noBytes;

	/* Some OSes include a call to access the system randomness data 
	   directly rather than having to go via a pseudo-device, if this 
	   capability is available then we use a direct read.  This currently 
	   applies to OpenBSD (added in 5.6, conveniently about the time that 
	   LibreSSL needed it) and Linux kernels from 3.17 (in response to 
	   prodding from LibreSSL and the appearance of the OpenBSD function).
	   
	   OpenBSD also has the older arc4random_buf(), which used to use
	   RC4 (ugh) until OpenBSD 5.5 when it was replaced by ChaCha20, which
	   postprocess the entropy data through the given stream cipher.  Since 
	   we're feeding the output into our own PRNG and since this function
	   is a general interface to the system randomness data, we use 
	   getentropy() rather than arc4random() */
#if defined( __linux__ ) && defined( GRND_NONBLOCK )
	/* getrandom() was defined in kernel 3.17 and above but is rarely
	   supported in libc ("if we add support for it then people might use it
	   and things won't work any more with older libc versions").  In some
	   cases it's possible to access it via syscall() with SYS_getrandom,
	   so the best that we can do is use that if it's available */
  #ifdef SYS_getrandom
	#include <sys/syscall.h>
	noBytes = syscall( SYS_getrandom, buffer, DEVRANDOM_BYTES, 
					   GRND_NONBLOCK );
	#ifdef DEBUG_RANDOM
	printf( __FILE__ ": getrandom() (via syscall()) contributed %d bytes.\n",
			noBytes );
	#endif /* DEBUG_RANDOM */
  #else
	/* noBytes = getrandom( buffer, DEVRANDOM_BYTES, GRND_NONBLOCK ); */
  #endif /* No guarantee of getrandom() support */
#elif defined( __OpenBSD__ ) && OpenBSD > 201412
	/* See the comment at the start for why we use 'OpenBSD' for the version 
	   number */
	noBytes = getentropy( buffer, DEVRANDOM_BYTES );
	if( noBytes == 0 )
		{
		/* OpenBSD's semantics for the call differ from the read()-alike
		   functionality of the Linux version and simply return 0 or -1
		   for success or failure, so we convert the former into a byte
		   count */
		noBytes = DEVRANDOM_BYTES;
		}
	#ifdef DEBUG_RANDOM
	printf( __FILE__ ": getentropy() contributed %d bytes.\n", noBytes );
	#endif /* DEBUG_RANDOM */
#elif ( defined( __FreeBSD__ ) || defined( __NetBSD__ ) || \
		defined( __OpenBSD__ ) || defined( __APPLE__ ) ) && \
	  defined( KERN_ARND )
	{
	static const int mib[] = { CTL_KERN, KERN_ARND };
	size_t size = DEVRANDOM_BYTES;
	int status;

	/* Alternative to getentropy() if it's not present, supported by some 
	   BSDs */
	noBytes = 0;
	if( sysctl( mib, 2, buffer, &size, NULL, 0 ) == 0 )
		noBytes = size;
	#ifdef DEBUG_RANDOM
	printf( __FILE__ ": sysctl( KERN_ARND ) contributed %d bytes.\n", 
			noBytes );
	#endif /* DEBUG_RANDOM */
	}
#else
	/* Check whether there's a /dev/random present.  We don't use O_NOFOLLOW 
	   because on some Unixen special files can be symlinks and in any case 
	   a system that allows attackers to mess with privileged filesystems 
	   like this is presumably a goner anyway */
	if( ( randFD = open( "/dev/urandom", O_RDONLY ) ) < 0 )
		return( 0 );
	if( randFD <= 2 )
		{
		/* We've been given a standard I/O handle, something's wrong */
		close( randFD );
		return( 0 );
		}

	/* Read data from /dev/urandom, which won't block (although the quality
	   of the noise is arguably slighly less).  We only assign this a 75% 
	   quality factor to ensure that we still get randomness from other 
	   sources as well.  Under FreeBSD 5.x and OS X, the /dev/random 
	   implementation is broken, using a pretend dev-random implemented with 
	   Yarrow and a 160-bit pool (animi sub vulpe latent) so we only assign 
	   a 60% quality factor.  These generators also lie about entropy, with 
	   both /random and /urandom being the same PRNG-based implementation.
	   The AIX /dev/random isn't an original /dev/random either but merely 
	   provides a compatible interface, taking its input from interrupt 
	   timings of a very small number of sources such as ethernet and SCSI 
	   adapters and postprocessing them with Yarrow.  This implementation is 
	   also a lot more conservative about its entropy estimation, such that 
	   the blocking interface blocks a lot more often than the original 
	   /dev/random implementation would.  In addition it stops gathering 
	   entropy (from interrupts) when it thinks it has enough, and only 
	   resumes when the value falls below a certain value.  OTOH this may
	   still be better than the Linux implementation, which in 2009
	   stopped gathering any information from interrupts at all by removing
	   the IRQF_SAMPLE_RANDOM flag.  Apparent intention was to replace it
	   with something else, but after much bikeshedding this never 
	   happened, which makes the Linux /dev/random particularly bad on 
	   headless and embedded systems */
	noBytes = read( randFD, buffer, DEVRANDOM_BYTES );
	close( randFD );
#endif /* OSes without API support for the randomness device */
	if( noBytes < 1 )
		{
#ifdef DEBUG_RANDOM
		printf( __FILE__ ": /dev/random (or equivalent) read failed.\n" );
#endif /* DEBUG_RANDOM */
		return( 0 );
		}
#ifdef DEBUG_RANDOM
	printf( __FILE__ ": /dev/random (or equivalent) contributed %d bytes.\n", 
			noBytes );
#endif /* DEBUG_RANDOM */
	setMessageData( &msgData, buffer, noBytes );
	krnlSendMessage( SYSTEM_OBJECT_HANDLE, IMESSAGE_SETATTRIBUTE_S, &msgData,
					 CRYPT_IATTRIBUTE_ENTROPY );
	zeroise( buffer, DEVRANDOM_BYTES );
	if( noBytes < DEVRANDOM_BYTES )
		return( 0 );
	krnlSendMessage( SYSTEM_OBJECT_HANDLE, IMESSAGE_SETATTRIBUTE,
					 ( MESSAGE_CAST ) &quality, 
					 CRYPT_IATTRIBUTE_ENTROPY_QUALITY );
	return( quality );
	}

/* egd/prngd interface */

CHECK_RETVAL \
static int getEGDdata( void )
	{
	static const char *egdSources[] = {
		"/var/run/egd-pool", "/dev/egd-pool", "/etc/egd-pool", NULL, NULL };
	MESSAGE_DATA msgData;
	BYTE buffer[ DEVRANDOM_BYTES + 8 ];
	static const int quality = 75;
	int egdIndex, sockFD, noBytes = CRYPT_ERROR, status;

	/* Look for the egd/prngd output.  We re-search each time because,
	   unlike /dev/random, it's both a user-level process and a movable
	   feast, so it can disappear and reappear at a different location
	   between runs */
	sockFD = socket( AF_UNIX, SOCK_STREAM, 0 );
	if( sockFD < 0 )
		return( 0 );
	for( egdIndex = 0; egdSources[ egdIndex ] != NULL && \
					   egdIndex < FAILSAFE_ARRAYSIZE( egdSources, char * ); 
		 egdIndex++ )
		{
		struct sockaddr_un sockAddr;

		memset( &sockAddr, 0, sizeof( struct sockaddr_un ) );
		sockAddr.sun_family = AF_UNIX;
		strlcpy_s( sockAddr.sun_path, sizeof( sockAddr.sun_path ), 
				   egdSources[ egdIndex ] );
		if( connect( sockFD, ( struct sockaddr * ) &sockAddr,
					 sizeof( struct sockaddr_un ) ) >= 0 )
			break;
		}
	ENSURES( egdIndex < FAILSAFE_ARRAYSIZE( egdSources, char * ) );
	if( egdSources[ egdIndex ] == NULL )
		{
		close( sockFD );
		return( 0 );
		}

	/* Read up to 128 bytes of data from the source:
		write:	BYTE 1 = read data nonblocking
				BYTE DEVRANDOM_BYTES = count
		read:	BYTE returned bytes
				BYTE[] data
	   As with /dev/random we only assign this a 75% quality factor to
	   ensure that we still get randomness from other sources as well */
	buffer[ 0 ] = 1;
	buffer[ 1 ] = DEVRANDOM_BYTES;
	status = write( sockFD, buffer, 2 );
	if( status == 2 )
		{
		status = read( sockFD, buffer, 1 );
		noBytes = buffer[ 0 ];
		if( status != 1 || noBytes < 0 || noBytes > DEVRANDOM_BYTES )
			status = -1;
		else
			status = read( sockFD, buffer, noBytes );
		}
	close( sockFD );
	if( ( status < 0 ) || ( status != noBytes ) )
		{
#ifdef DEBUG_RANDOM
	printf( __FILE__ ": EGD (%s) read failed.\n", egdSources[ egdIndex ] );
#endif /* DEBUG_RANDOM */
		return( 0 );
		}

	/* Send the data to the pool */
#ifdef DEBUG_RANDOM
	printf( __FILE__ ": EGD (%s) contributed %d bytes.\n",
			egdSources[ egdIndex ], noBytes );
#endif /* DEBUG_RANDOM */
	setMessageData( &msgData, buffer, noBytes );
	krnlSendMessage( SYSTEM_OBJECT_HANDLE, IMESSAGE_SETATTRIBUTE_S, &msgData,
					 CRYPT_IATTRIBUTE_ENTROPY );
	zeroise( buffer, DEVRANDOM_BYTES );
	if( noBytes < DEVRANDOM_BYTES )
		return( 0 );
	krnlSendMessage( SYSTEM_OBJECT_HANDLE, IMESSAGE_SETATTRIBUTE,
					 ( MESSAGE_CAST ) &quality, 
					 CRYPT_IATTRIBUTE_ENTROPY_QUALITY );
	return( quality );
	}

/****************************************************************************
*																			*
*						Last-resort External-Source Polling					*
*																			*
****************************************************************************/

#ifndef NO_SYSV_SHAREDMEM

#if defined( __MVS__ ) || defined( __hpux ) || defined( __Android__ )

/* MVS USS, PHUX, and the Android version of Linux don't have wait4() so we 
   emulate it with waitpid() and getrusage() */

CHECK_RETVAL STDC_NONNULL_ARG( ( 2, 4 ) ) \
pid_t wait4( pid_t pid, OUT int *status, int options, 
			 OUT struct rusage *rusage )
	{
	const pid_t waitPid = waitpid( pid, status, options );

	getrusage( RUSAGE_CHILDREN, rusage );
	return( waitPid );
	}
#endif /* MVS USS || PHUX || Android */

/* Cray Unicos and QNX 4.x have neither wait4() nor getrusage, so we fake
   it */

#if defined( _CRAY ) || ( defined( __QNX__ ) && OSVERSION <= 4 )

CHECK_RETVAL STDC_NONNULL_ARG( ( 2, 4 ) ) \
pid_t wait4( pid_t pid, OUT int *status, int options, 
			 OUT struct rusage *rusage )
	{
	return( waitpid( pid, status, options ) );
	}
#endif /* Cray Unicos || QNX 4.x */

#if !defined( _POSIX_PRIORITY_SCHEDULING ) || ( _POSIX_PRIORITY_SCHEDULING < 0 )
  /* No sched_yield() or sched_yield() not supported */
  #define sched_yield()
#elif ( _POSIX_PRIORITY_SCHEDULING == 0 )

static void my_sched_yield( void )
	{
	/* sched_yield() is only supported if sysconf() tells us that it is */
	if( sysconf( _SC_PRIORITY_SCHEDULING ) > 0 )
		sched_yield();
	}
#define sched_yield				my_sched_yield

#endif /* Systems without sched_yield() */

/* When exiting from the child, we call _exit() rather than exit() since 
   this skips certain cleanup operations (atexit() and signal handlers).
   More technically, _exit() is a system call that performs kernel-space
   cleanup while exit() also performs user-space cleanup */
	  
#define CHILD_EXIT( status )	_exit( status )

/* A special form of the ENSURES() predicate used in the forked child 
   process, which calls CHILD_EXIT() rather than returning */

#define ENSURES_EXIT( x ) \
		if( !( x ) ) { assert( INTERNAL_ERROR ); CHILD_EXIT( -1 ); }

/* Under SunOS 4.x popen() doesn't record the pid of the child process.  When
   pclose() is called, instead of calling waitpid() for the correct child, it
   calls wait() repeatedly until the right child is reaped.  The problem whit
   this behaviour is that this reaps any other children that happen to have
   died at that moment, and when their pclose() comes along, the process hangs
   forever.

   This behaviour may be related to older SVR3-compatible SIGCLD handling in
   which, under the SIG_IGN disposition, the status of the child was discarded
   (i.e. no zombies were generated) so that when the parent called wait() it
   would block until all children terminated, whereupon wait() would return -1
   with errno set to ECHILD.

   The fix for this problem is to use a wrapper for popen()/pclose() that
   saves the pid in the dataSources structure (code adapted from GNU-libc's
   popen() call).  Doing our own popen() has other advantages as well, for
   example we use the more secure execl() to run the child instead of the
   dangerous system().

   Aut viam inveniam aut faciam */

CHECK_RETVAL STDC_NONNULL_ARG( ( 1 ) ) \
static FILE *my_popen( INOUT DATA_SOURCE_INFO *entry )
	{
	static uid_t gathererUID = ( uid_t ) -1, gathererGID = ( uid_t ) -1;
	int pipedes[ 2 + 8 ];
	FILE *stream;

	/* Sanity check for stdin and stdout */
	REQUIRES_N( STDIN_FILENO <= 1 && STDOUT_FILENO <= 1 );

	/* If we're root, get UID/GID information so we can give up our 
	   permissions to make sure that we don't inadvertently read anything 
	   sensitive.  We do it at this point in order to avoid calling 
	   getpwnam() between the fork() and the execl() since some getpwnam()s
	   may call malloc() which could be locked by another thread which the
	   child won't have access to */
	if( geteuid() == 0 && gathererUID == ( uid_t ) -1 )
		{
		struct passwd *passwd;

		passwd = getpwnam( "nobody" );
		if( passwd != NULL )
			{
			gathererUID = passwd->pw_uid;
			gathererGID = passwd->pw_gid;
			}
		else
			{
			assert( DEBUG_WARN );
			}
		}

	/* Create the pipe.  Note that under QNX the pipe resource manager
	   'pipe' must be running in order to use pipes */
	if( pipe( pipedes ) < 0 )
		return( NULL );

	/* Fork off the child.  In theory we could use vfork() ("vfork() is like 
	   an OS orgasm.  All OSes want to do it, but most just end up faking 
	   it" - Chris Wedgwood), but most modern Unixen use copy-on-write for 
	   forks anyway (with vfork() being just an alias for fork()), so we get 
	   most of the benefits of vfork() with a plain fork().  There is 
	   however another problem with fork that isn't fixed by COW.  Any large 
	   program, when forked, requires (at least temporarily) a lot of 
	   address space.  That is, when the process is forked the system needs 
	   to allocate many virtual pages (backing store) even if those pages 
	   are never used.  If the system doesn't have enough swap space 
	   available to support this, the fork() will fail when the system tries 
	   to reserver backing store for pages that are never touched.  Even in 
	   non-large processes this can cause problems when (as with the 
	   randomness-gatherer) many children are forked at once.  However this 
	   is a rather unlikely situation, and since the fork()-based entropy-
	   gathering is used only as a last resort when all other methods have
	   failed, we rarely get to this code, let alone run it in a situation
	   where the problem described above crops up.

	   In the absence of threads the use of pcreate() (which only requires
	   backing store for the new processes' stack, not the entire process)
	   would do the trick, however pcreate() isn't compatible with threads,
	   which makes it of little use for the default thread-enabled cryptlib
	   build */
	entry->pid = fork();
	if( entry->pid == ( pid_t ) -1 )
		{
		/* The fork failed */
		close( pipedes[ 0 ] );
		close( pipedes[ 1 ] );
		return( NULL );
		}

	if( entry->pid == ( pid_t ) 0 )
		{
		int fd;

		/* We are the child, connect the read side of the pipe to stdout and
		   unplug stdin and stderr */
		if( dup2( pipedes[ STDOUT_FILENO ], STDOUT_FILENO ) < 0 )
			CHILD_EXIT( 127 );
		if( ( fd = open( "/dev/null", O_RDWR ) ) > 0 )
			{
			dup2( fd, STDIN_FILENO );
			dup2( fd, STDERR_FILENO );
			close( fd );
			}

		/* Give up our permissions if required to make sure that we don't 
		   inadvertently read anything sensitive.  We don't check whether 
		   the change succeeds since it's not a major security problem but 
		   just a precaution (in theory an attacker could do something like 
		   fork()ing until RLIMIT_NPROC is reached, at which point it'd 
		   fail, but that doesn't really give them anything) */
		if( gathererUID != ( uid_t ) -1 )
			{
#if 0		/* Not available on some OSes */
			( void ) setuid( gathererUID );
			( void ) seteuid( gathererUID );
			( void ) setgid( gathererGID );
			( void ) setegid( gathererGID );
#else
  #if( defined( __linux__ ) || ( defined( __FreeBSD__ ) && OSVERSION >= 5 ) || \
	   ( defined( __hpux ) && OSVERSION >= 11 ) )
			( void ) setresuid( gathererUID, gathererUID, gathererUID );
			( void ) setresgid( gathererGID, gathererGID, gathererGID );
  #else
			( void ) setreuid( gathererUID, gathererUID );
			( void ) setregid( gathererGID, gathererGID );
  #endif /* OSses with setresXid() */
#endif /* 0 */
			}

		/* Close the pipe descriptors */
		close( pipedes[ STDIN_FILENO ] );
		close( pipedes[ STDOUT_FILENO ] );

		/* Try and exec the program */
		execl( entry->path, entry->path, entry->arg, NULL );

		/* Die if the exec failed */
		CHILD_EXIT( 127 );
		}

	/* We are the parent.  Close the irrelevant side of the pipe and open the
	   relevant side as a new stream.  Mark our side of the pipe to close on
	   exec, so new children won't see it (if this call fails there's not 
	   much that we can do, and it's mostly a hygiene thing so we don't fail
	   fatally on it) */
	close( pipedes[ STDOUT_FILENO ] );
	( void ) fcntl( pipedes[ STDIN_FILENO ], F_SETFD, FD_CLOEXEC );
	stream = fdopen( pipedes[ STDIN_FILENO ], "r" );
	if( stream == NULL )
		{
		int savedErrno = errno;

		/* The stream couldn't be opened or the child structure couldn't be
		   allocated.  Kill the child and close the other side of the pipe */
		kill( entry->pid, SIGKILL );
		close( pipedes[ STDOUT_FILENO ] );
		waitpid( entry->pid, NULL, 0 );
		entry->pid = 0;
		errno = savedErrno;
		return( NULL );
		}

	return( stream );
	}

CHECK_RETVAL STDC_NONNULL_ARG( ( 1, 2 ) ) \
static int my_pclose( INOUT DATA_SOURCE_INFO *entry, 
					  INOUT struct rusage *rusage )
	{
	pid_t pid;
	int iterationCount = 0, status = 0;

	/* Close the pipe */
	fclose( entry->pipe );
	entry->pipe = NULL;

	/* Wait for the child to terminate, ignoring the return value from the
	   process because some programs return funny values that would result
	   in the input being discarded even if they executed successfully.
	   This isn't a problem because the result data size threshold will
	   filter out any programs that exit with a usage message without
	   producing useful output */
	do
		{
		/* We use wait4() instead of waitpid() to get the last bit of
		   entropy data, the resource usage of the child */
		pid = wait4( entry->pid, NULL, 0, rusage );
		}
	while( pid == -1 && errno == EINTR && \
		   iterationCount++ < FAILSAFE_ITERATIONS_MED );
	if( pid != entry->pid )
		status = -1;
	entry->pid = 0;

	return( status );
	}

/* Get data from an external entropy source */

CHECK_RETVAL STDC_NONNULL_ARG( ( 1, 2, 4 ) ) \
static int getEntropySourceData( INOUT DATA_SOURCE_INFO *dataSource, 
								 OUT_BUFFER( bufSize, *bufPos ) BYTE *bufPtr, 
								 IN_DATALENGTH const int bufSize, 
								 OUT_DATALENGTH_Z int *bufPos )
	{
	int bufReadPos = 0, bufWritePos = 0;
	size_t noBytes;

	/* Try and get more data from the source.  If we get zero bytes, the
	   source has sent us all it has */
	if( ( noBytes = fread( bufPtr, 1, bufSize, dataSource->pipe ) ) <= 0 )
		{
		struct rusage rusage;
		int total = 0;

		/* If there's a problem, exit */
		if( my_pclose( dataSource, &rusage ) != 0 )
			return( 0 );

		/* Try and estimate how much entropy we're getting from a data
		   source */
		if( dataSource->usefulness != 0 )
			{
			if( dataSource->usefulness < 0 )
				{
				/* Absolute rating, 1024 / -n */
				total = 1025 / -dataSource->usefulness;
				}
			else
				{
				/* Relative rating, 1024 * n */
				total = dataSource->length / dataSource->usefulness;
				}
			}
#ifdef DEBUG_RANDOM
		printf( __FILE__ ": %s %s contributed %d bytes (compressed), "
				"usefulness = %d.\n", dataSource->path,
				( dataSource->arg != NULL ) ? dataSource->arg : "",
				dataSource->length, total );
#endif /* DEBUG_RANDOM */

		/* Copy in the last bit of entropy data, the resource usage of the
		   popen()ed child */
		if( sizeof( struct rusage ) < bufSize )
			{
			memcpy( bufPtr, &rusage, sizeof( struct rusage ) );
			*bufPos += sizeof( struct rusage );
			}

		return( total );
		}

	/* Run-length compress the input byte sequence */
	while( bufReadPos < noBytes )
		{
		const int ch = byteToInt( bufPtr[ bufReadPos ] );

		/* If it's a single byte or we're at the end of the buffer, just
		   copy it over */
		if( bufReadPos >= bufSize - 1 || ch != bufPtr[ bufReadPos + 1 ] )
			{
			bufPtr[ bufWritePos++ ] = intToByte( ch );
			bufReadPos++;
			}
		else
			{
			int count = 0;

			/* It's a run of repeated bytes, replace them with the byte
			   count mod 256 */
			while( bufReadPos < noBytes && ( ch == bufPtr[ bufReadPos ] ) )
				{
				count++;
				bufReadPos++;
				}
			bufPtr[ bufWritePos++ ] = intToByte( count );
			}
		}

	/* Remember the number of (compressed) bytes of input that we obtained */
	*bufPos += bufWritePos;
	dataSource->length += noBytes;

	return( 0 );
	}

/* The child process that performs the polling, forked from slowPoll() */

#define SLOWPOLL_TIMEOUT	30		/* Time out after 30 seconds */

static void childPollingProcess( const int existingEntropy )
	{
	GATHERER_INFO *gathererInfo;
	MONOTIMER_INFO timerInfo;
	BOOLEAN moreSources;
	struct timeval tv;
	struct rlimit rl = { 0, 0 };
	fd_set fds;
#if defined( __hpux )
	size_t maxFD = 0;
#else
	int maxFD = 0;
#endif /* OS-specific brokenness */
	int usefulness = 0, fdIndex, bufPos, i, iterationCount, status;

	/* General housekeeping: Make sure that we can never dump core, and close
	   all inherited file descriptors.  We need to do this because if we
	   don't and the calling app has FILE *'s open, these will be flushed
	   if we call exit() in the child and again when the parent writes to
	   them or closes them, resulting in everything that was present in the
	   FILE * buffer at the time of the fork() being written twice.  An
	   alternative solution would be to call _exit() instead of exit() 
	   (which is the default action for the CHILD_EXIT() macro), but this is 
	   somewhat system-dependant and isn't present in all cases so we still
	   take the precaution of exit()-proofing the code.
	   
	   Note that we don't close any of the standard handles because this 
	   could lead to the next file being opened being given the stdin/stdout/
	   stderr handle, which in general is just a nuisance but then some 
	   older kernels didn't check handles when running a setuid program so 
	   that it was actually an exploitable flaw.  In addition some later 
	   kernels (e.g. NetBSD) overreact to the problem a bit and complain 
	   when they see a setuid program with stdin/stdout/stderr closed, so 
	   it's a good idea to leave these open.  We could in theory close them
	   anyway and reopen them to /dev/null, but it's not clear whether this
	   really buys us anything.

	   In addition to this we should in theory call cryptEnd() since we
	   don't need any cryptlib objects beyond this point and it'd be a good
	   idea to clean them up to get rid of sensitive data held in memory.
	   However in some cases when using a crypto device or network interface
	   or similar item the shutdown in the child will also shut down the
	   parent item because while cryptlib objects are reference-counted the
	   external items aren't (they're beyond the control of cryptlib).  Even
	   destroying just contexts with keys loaded isn't possible because they
	   may be tied to a device that will propagate the shutdown from the
	   child to the parent via the device.

	   In general the child will be short-lived, and the fact that any modern 
	   fork() will have copy-on-write semantics will mean that cryptlib 
	   memory is never copied to the child and further children.  It would, 
	   however, be better if there were some way to perform a neutron-bomb 
	   type shutdown that only zeroises senstive information while leaving 
	   structures intact */
	setrlimit( RLIMIT_CORE, &rl );
	for( fdIndex = getdtablesize() - 1; fdIndex > STDOUT_FILENO; fdIndex-- )
		close( fdIndex );
	fclose( stderr );	/* Arrghh!!  It's Stuart code!! */

	/* Fire up each randomness source */
	FD_ZERO( &fds );
	for( i = 0; dataSources[ i ].path != NULL && \
				i < FAILSAFE_ARRAYSIZE( dataSources, DATA_SOURCE_INFO ); i++ )
		{
		/* Check for the end-of-lightweight-sources marker */
		if( dataSources[ i ].path[ 0 ] == '\0' )
			{
			/* If we're only polling lightweight sources because we've
			   already obtained entropy from additional sources,we're
			   done */
			if( existingEntropy >= 50 )
				{
#ifdef DEBUG_RANDOM
				puts( __FILE__ ": All lightweight sources polled, exiting "
					  "without polling\nheavyweight ones." );
#endif /* DEBUG_RANDOM */
				break;
				}

			/* We're polling all sources, continue with the heavyweight
			   ones */
			continue;
			}

		/* Since popen() is a fairly heavyweight function, we check to see 
		   whether the executable exists before we try to run it */
		if( access( dataSources[ i ].path, X_OK ) )
			{
#ifdef DEBUG_RANDOM
			printf( __FILE__ ": %s not present%s.\n", dataSources[ i ].path,
					dataSources[ i ].hasAlternative ? \
						", has alternatives" : "" );
#endif /* DEBUG_RANDOM */
			dataSources[ i ].pipe = NULL;
			}
		else
			dataSources[ i ].pipe = my_popen( &dataSources[ i ] );
		if( dataSources[ i ].pipe == NULL )
			continue;
		if( fileno( dataSources[ i ].pipe ) >= FD_SETSIZE )
			{
			/* The fd is larger than what can be fitted into an fd_set, don't
			   try and use it.  This can happen if the calling app opens a
			   large number of files, since most FD_SET() macros don't
			   perform any safety checks this can cause segfaults and other
			   problems if we don't perform the check ourselves */
			fclose( dataSources[ i ].pipe );
			dataSources[ i ].pipe = NULL;
			continue;
			}

		/* Set up the data source information */
		dataSources[ i ].pipeFD = fileno( dataSources[ i ].pipe );
		if( dataSources[ i ].pipeFD > maxFD )
			maxFD = dataSources[ i ].pipeFD;
		fcntl( dataSources[ i ].pipeFD, F_SETFL, O_NONBLOCK );
		FD_SET( dataSources[ i ].pipeFD, &fds );
		dataSources[ i ].length = 0;

		/* If there are alternatives for this command, don't try and execute
		   them */
		iterationCount = 0;
		while( dataSources[ i ].path != NULL && \
			   dataSources[ i ].hasAlternative && \
			   i < FAILSAFE_ARRAYSIZE( dataSources, DATA_SOURCE_INFO ) && \
			   iterationCount++ < FAILSAFE_ITERATIONS_MED ) 
			{
#ifdef DEBUG_RANDOM
			printf( __FILE__ ": Skipping %s.\n", dataSources[ i + 1 ].path );
#endif /* DEBUG_RANDOM */
			i++;
			}
		ENSURES_EXIT( iterationCount < FAILSAFE_ITERATIONS_MED );
					  /* i is checked as part of the loop control */
		}
	ENSURES_EXIT( i < FAILSAFE_ARRAYSIZE( dataSources, DATA_SOURCE_INFO ) );
	gathererInfo = ( GATHERER_INFO * ) gathererBuffer;
	bufPos = sizeof( GATHERER_INFO );	/* Start of buf.has status info */

	/* Suck up all of the data that we can get from each of the sources */
	status = setMonoTimer( &timerInfo, SLOWPOLL_TIMEOUT );
	ENSURES_EXIT( cryptStatusOK( status ) );
	for( moreSources = TRUE, iterationCount = 0;
		 moreSources && bufPos < gathererBufSize && \
			iterationCount < FAILSAFE_ITERATIONS_MAX; 
		 iterationCount++ )
		{
		/* Wait for data to become available from any of the sources, with a
		   timeout of 10 seconds.  This adds even more randomness since data
		   becomes available in a nondeterministic fashion.  Kudos to HP's QA
		   department for managing to ship a select() that breaks its own
		   prototype */
		tv.tv_sec = 10;
		tv.tv_usec = 0;
#if defined( __hpux ) && ( OSVERSION == 9 || OSVERSION == 0 )
		if( select( maxFD + 1, ( int * ) &fds, NULL, NULL, &tv ) == -1 )
#else
		if( select( maxFD + 1, &fds, NULL, NULL, &tv ) == -1 )
#endif /* __hpux */
			break;

		/* One of the sources has data available, read it into the buffer */
		for( i = 0; dataSources[ i ].path != NULL && \
					i < FAILSAFE_ARRAYSIZE( dataSources, DATA_SOURCE_INFO ); 
			 i++ )
			{
			if( dataSources[ i ].pipe != NULL && \
				FD_ISSET( dataSources[ i ].pipeFD, &fds ) )
				{
				usefulness += getEntropySourceData( &dataSources[ i ],
													gathererBuffer + bufPos,
													gathererBufSize - bufPos,
													&bufPos );
				}
			}
		ENSURES_EXIT( i < FAILSAFE_ARRAYSIZE( dataSources, DATA_SOURCE_INFO ) );

		/* Check if there's more input available on any of the sources */
		moreSources = FALSE;
		FD_ZERO( &fds );
		for( i = 0; dataSources[ i ].path != NULL && \
					i < FAILSAFE_ARRAYSIZE( dataSources, DATA_SOURCE_INFO ); 
			 i++ )
			{
			if( dataSources[ i ].pipe != NULL )
				{
				FD_SET( dataSources[ i ].pipeFD, &fds );
				moreSources = TRUE;
				}
			}
		ENSURES_EXIT( i < FAILSAFE_ARRAYSIZE( dataSources, DATA_SOURCE_INFO ) );

		/* If we've gone over our time limit, kill anything still hanging
		   around and exit.  This prevents problems with input from blocked
		   sources */
		if( checkMonoTimerExpired( &timerInfo ) )
			{
			for( i = 0; dataSources[ i ].path != NULL && \
						i < FAILSAFE_ARRAYSIZE( dataSources, DATA_SOURCE_INFO ); 
				 i++ )
				{
				if( dataSources[ i ].pipe != NULL )
					{
#ifdef DEBUG_RANDOM
					printf( __FILE__ ": Aborting read of %s due to "
							"timeout.\n", dataSources[ i ].path );
#endif /* DEBUG_RANDOM */
					fclose( dataSources[ i ].pipe );
					kill( dataSources[ i ].pid, SIGKILL );
					dataSources[ i ].pipe = NULL;
					dataSources[ i ].pid = 0;
					}
				}
			ENSURES_EXIT( i < FAILSAFE_ARRAYSIZE( dataSources, DATA_SOURCE_INFO ) );
			moreSources = FALSE;
#ifdef DEBUG_RANDOM
			puts( __FILE__ ": Poll timed out, probably due to blocked data "
				  "source." );
#endif /* DEBUG_RANDOM */
			}
		}
	ENSURES_EXIT( iterationCount < FAILSAFE_ITERATIONS_MAX );
	gathererInfo->usefulness = usefulness;
	gathererInfo->noBytes = bufPos;
#ifdef DEBUG_RANDOM
	printf( __FILE__ ": Got %d bytes, usefulness = %d.\n", bufPos,
			usefulness );
#endif /* DEBUG_RANDOM */

	/* "Thou child of the daemon, ... wilt thou not cease...?"
	   -- Acts 13:10 */
	CHILD_EXIT( 0 );
	}

/* Unix external-source slow poll.  If a few of the randomness sources 
   create a large amount of output then the slowPoll() stops once the buffer 
   has been filled (but before all of the randomness sources have been 
   sucked dry) so that the 'usefulness' factor remains below the threshold.  
   For this reason the gatherer buffer has to be fairly sizeable on 
   moderately loaded systems.

   An alternative strategy, suggested by Massimo Squillace, is to use a 
   chunk of shared memory protected by a semaphore, with the first 
   sizeof( int ) bytes at the start serving as a high-water mark.  The 
   process forks and waitpid()'s for the child's pid.  The child forks all 
   the entropy-gatherers and exits, allowing the parent to resume execution. 
   The child's children are inherited by init (double-fork paradigm), when 
   each one is finished it takes the semaphore, writes data to the shared 
   memory segment at the given offset, updates the offset, releases the 
   semaphore again, and exits, to be reaped by init.

   The parent monitors the shared memory offset and when enough data is 
   available takes the semaphore, grabs the data, and releases the shared 
   memory area and semaphore.  If any children are still running they'll get 
   errors when they try to access the semaphore or shared memory and 
   silently exit.

   This approach has the advantage that all of the forked processes are 
   managed by init rather than having the parent have to wait for them, but 
   the disadvantage that the end-of-job handling is rather less rigorous. 
   An additional disadvantage is that the existing code has had a lot of 
   real-world testing and adaptation to system-specific quirks, which would 
   have to be repeated for any new version */

#define SHARED_BUFSIZE		49152	/* Usually about 25K are filled */

static void externalSourcesPoll( const int existingEntropy )
	{
	const int pageSize = getSysVar( SYSVAR_PAGESIZE );

	/* Check whether a non-default SIGCHLD handler is present.  This is 
	   necessary because if the program that cryptlib is a part of installs 
	   its own handler it will end up reaping the cryptlib children before
	   cryptlib can.  As a result my_pclose() will call waitpid() on a
	   process that has already been reaped by the installed handler and
	   return an error, so the read data won't be added to the randomness
	   pool */
	if( sigaction( SIGCHLD, NULL, &gathererOldHandler ) < 0 )
		{
		/* This assumes that stderr is open, i.e. that we're not a daemon
		   (this should be the case at least during the development/debugging
		   stage) */
		fprintf( stderr, "cryptlib: sigaction() failed, errno = %d, "
				 "file " __FILE__ ", line %d.\n", errno, __LINE__ );
		abort();
		}

	/* Check for handler override */
	if( gathererOldHandler.sa_handler != SIG_DFL && \
		gathererOldHandler.sa_handler != SIG_IGN )
		{
#ifdef DEBUG_CONFLICTS
		/* We overwrote the caller's handler, warn them about this */
		fprintf( stderr, "cryptlib: Conflicting SIGCHLD handling detected "
				 "in randomness polling code,\nfile " __FILE__ ", line %d.  "
				 "See the source code for more\ninformation.\n", __LINE__ );
#endif /* DEBUG_CONFLICTS */
		}

	/* If a non-default handler is present, replace it with the default 
	   handler */
	if( gathererOldHandler.sa_handler != SIG_DFL )
		{
		struct sigaction newHandler;

		memset( &newHandler, 0, sizeof( newHandler ) );
		newHandler.sa_handler = SIG_DFL;
		sigemptyset( &newHandler.sa_mask );
		sigaction( SIGCHLD, &newHandler, NULL );
		}

	/* Set up the shared memory */
	gathererBufSize = ( SHARED_BUFSIZE / pageSize ) * ( pageSize + 1 );
	if( ( gathererMemID = shmget( IPC_PRIVATE, gathererBufSize,
								  IPC_CREAT | 0600 ) ) == -1 || \
		( gathererBuffer = ( BYTE * ) shmat( gathererMemID,
											 NULL, 0 ) ) == ( BYTE * ) -1 )
		{
		/* There was a problem obtaining the shared memory, warn the user
		   and exit */
#ifdef _CRAY
		if( errno == ENOSYS )
			{
			/* Unicos supports shmget/shmat, but older Crays don't implement
			   it and return ENOSYS */
			fprintf( stderr, "cryptlib: SYSV shared memory required for "
					 "random number gathering isn't\n  supported on this "
					 "type of Cray hardware (ENOSYS),\n  file " __FILE__ 
					 ", line %d.\n", __LINE__ );
			}
#endif /* Cray */
#ifdef DEBUG_CONFLICTS
		fprintf( stderr, "cryptlib: shmget()/shmat() failed, errno = %d, "
				 "file " __FILE__ ", line %d.\n", errno, __LINE__ );
#endif /* DEBUG_CONFLICTS */
		if( gathererMemID != -1 )
			shmctl( gathererMemID, IPC_RMID, NULL );
		if( gathererOldHandler.sa_handler != SIG_DFL )
			sigaction( SIGCHLD, &gathererOldHandler, NULL );
		unlockPollingMutex();
		return; /* Something broke */
		}

	/* At this point we have a possible race condition since we need to set
	   the gatherer PID value inside the mutex but messing with mutexes
	   across a fork() is somewhat messy.  To resolve this, we set the PID
	   to a nonzero value (which marks it as busy) and exit the mutex, then
	   overwrite it with the real PID (also nonzero) from the fork */
	gathererProcess = -1;
	unlockPollingMutex();

	/* Fork off the gatherer, the parent process returns to the caller.  
	
	   Programs using the OS X Core Foundation framework will complain if a 
	   program calls fork() and doesn't follow it up with an exec() (which 
	   really screws up daemonization ), printing an error message:

		The process has forked and you cannot use this CoreFoundation \
		functionality safely. You MUST exec().

	   There are workarounds possible but they're daemon-specific and 
	   involve running under launchd, which isn't really an option here.
	   For now this is left as an OS X framework problem, there doesn't
	   seem to be anything that we can do to fix it here */
	if( ( gathererProcess = fork() ) != 0 )
		{
		/* If we're the parent, we're done */
		if( gathererProcess != -1 )
			return;

		/* The fork() failed, clean up and reset the gatherer PID to make 
		   sure that we're not locked out of retrying the poll later */
#ifdef DEBUG_CONFLICTS
		fprintf( stderr, "cryptlib: fork() failed, errno = %d, file " 
				 __FILE__ ", line %d.\n", errno, __LINE__ );
#endif /* DEBUG_CONFLICTS */
		lockPollingMutex();
		shmctl( gathererMemID, IPC_RMID, NULL );
		if( gathererOldHandler.sa_handler != SIG_DFL )
			sigaction( SIGCHLD, &gathererOldHandler, NULL );
		gathererProcess = 0;
		unlockPollingMutex();
		return;
		}

	/* Make the child an explicitly distinct function */
	childPollingProcess( existingEntropy );
	}

static int externalSourcesPollComplete( const BOOLEAN force )
	{
	MESSAGE_DATA msgData;
	GATHERER_INFO *gathererInfo = ( GATHERER_INFO * ) gathererBuffer;
	int quality, status;

	lockPollingMutex();
	if( gathererProcess	<= 0 )
		{
		/* There's no gatherer running, exit */
		unlockPollingMutex();

		return( CRYPT_OK );
		}

	/* If this is a forced shutdown, be fairly assertive with the gathering 
	   process */
	if( force )
		{
		/* Politely ask the the gatherer to shut down and (try and) yield 
		   our timeslice a few times so that the shutdown can take effect. 
		   This is unfortunately somewhat implementation-dependant in that 
		   in some cases it'll only yield the current thread's timeslice 
		   rather than the overall process' timeslice, or if it's a high-
		   priority thread it'll be scheduled again before any lower-
		   priority threads get to run */
		kill( gathererProcess, SIGTERM );
		sched_yield();
		sched_yield();
		sched_yield();	/* Well, sync is done three times too... */

		/* If the gatherer is still running, ask again, less politely this 
		   time */
		if( kill( gathererProcess, 0 ) != -1 || errno != ESRCH )
			kill( gathererProcess, SIGKILL );
		}

	/* Wait for the gathering process to finish and, if it was sucessful, 
	   add the randomness that it's gathered */
	if( waitpid( gathererProcess, &status, 0 ) >= 0 && WIFEXITED( status ) )
		{
		/* The child terminated normally, forward its output to the system 
		   device.  We don't check for errors at this point (apart from 
		   warning in the debug version) since this is an invisible internal 
		   routine for which we can't easily recover from problems.  Any 
		   problems are caught at a higher level by the randomness-quality 
		   checking */
		if( gathererInfo->noBytes > 0 && !force )
			{
			quality = min( gathererInfo->usefulness * 5, 100 );	/* 0-20 -> 0-100 */
			setMessageData( &msgData, gathererBuffer, gathererInfo->noBytes );
			status = krnlSendMessage( SYSTEM_OBJECT_HANDLE,
									  IMESSAGE_SETATTRIBUTE_S,
									  &msgData, CRYPT_IATTRIBUTE_ENTROPY );
			assert( cryptStatusOK( status ) );
			if( quality > 0 )
				{
				/* On some very cut-down embedded systems the entropy 
				   quality can be zero so we only send a quality estimate if 
				   there's actually something there */
				status = krnlSendMessage( SYSTEM_OBJECT_HANDLE,
										  IMESSAGE_SETATTRIBUTE, &quality,
										  CRYPT_IATTRIBUTE_ENTROPY_QUALITY );
				assert( cryptStatusOK( status ) );
				}
			}
		}
	zeroise( gathererBuffer, gathererBufSize );

	/* Detach and delete the shared memory (the latter is necessary because 
	   otherwise the unused ID hangs around until the process terminates) 
	   and restore the original signal handler if we replaced someone else's 
	   one */
	shmdt( gathererBuffer );
	shmctl( gathererMemID, IPC_RMID, NULL );
	if( gathererOldHandler.sa_handler != SIG_DFL )
		{
		struct sigaction oact;

		/* We replaced someone else's handler for the slow poll, reinstate 
		   the original one.  Since someone else could have in turn replaced 
		   our handler, we check for this and warn the user if necessary */
		sigaction( SIGCHLD, NULL, &oact );
		if( oact.sa_handler != SIG_DFL )
			{
#ifdef DEBUG_CONFLICTS
			/* The current handler isn't the one that we installed, warn the 
			   user */
			fprintf( stderr, "cryptlib: SIGCHLD handler was replaced "
					 "while slow poll was in progress,\nfile " __FILE__
					 ", line %d.  See the source code for more\n"
					 "information.\n", __LINE__ );
#endif /* DEBUG_CONFLICTS */
			}
		else
			{
			/* Our handler is still in place, replace it with the original 
			   one */
			sigaction( SIGCHLD, &gathererOldHandler, NULL );
			}
		}
	gathererProcess = 0;
	unlockPollingMutex();

	return( CRYPT_OK );
	}
#endif /* NO_SYSV_SHAREDMEM */

/****************************************************************************
*																			*
*									Slow Poll								*
*																			*
****************************************************************************/

/* Slow poll.  We try for sources that are directly accessible 
   programmatically and only fall back to the external-sources poll as a 
   last resort (this is rarely, if ever, required) */

void slowPoll( void )
	{
	int extraEntropy = 0;

	/* Make sure that we don't start more than one slow poll at a time.  The
	   gathererProcess value may be positive (a PID) or -1 (error), so we
	   compare it to the specific value 0 (= not-used) in the check */
	lockPollingMutex();
	if( gathererProcess != 0 )
		{
		unlockPollingMutex();
		return;
		}

	/* The popen()-level slow poll is the screen-scraping interface of last
	   resort that we use only if we can't get the entropy in any other
	   way.  If the system provides entropy from alternate sources, we don't 
	   have have to try the screen-scraping slow poll (a number of these 
	   additional sources, things like procfs and kstats, duplicate the 
	   sources polled in the slow poll anyway, so we're not adding much by 
	   polling these extra sources if we've already got the data directly) */
	extraEntropy += getDevRandomData();
	if( !access( "/proc/interrupts", R_OK ) )
		extraEntropy += getProcFSdata();
	extraEntropy += getEGDdata();
#ifdef USE_KSTAT
	extraEntropy += getKstatData();
#endif /* USE_KSTAT */
#ifdef USE_PROC
	extraEntropy += getProcData();
#endif /* USE_PROC */
#ifdef USE_SYSCTL
	extraEntropy += getSysctlData();
#endif /* USE_SYSCTL */
#ifdef __iOS__ 
	extraEntropy += getIOSData();
#endif /* __iOS__  */
#ifdef DEBUG_RANDOM
	printf( __FILE__ ": Got %d additional entropy from direct sources.\n",
			extraEntropy );
	if( extraEntropy >= 100 )
		{
		puts( "  (Skipping full slowpoll since sufficient entropy is "
			  "available)." );
		}
#endif /* DEBUG_RANDOM */
	if( extraEntropy >= 100 )
		{
		/* We got enough entropy from the additional sources, we don't
		   have to go through with the full external-sources poll */
		unlockPollingMutex();
		return;
		}

	/* A few systems don't support SYSV shared memory so we can't go beyond 
	   this point, all that we can do is warn the user that they'll have to 
	   use the entropy mechanisms intended for embedded systems without 
	   proper entropy sources */
#ifdef NO_SYSV_SHAREDMEM
	fprintf( stderr, "cryptlib: This system doesn't contain the OS "
			 "mechanisms required to provide\n          system entropy "
			 "sources that can be used for key generation.  In\n"
			 "          order to use cryptlib in this environment, you "
			 "need to apply the\n          randomness mechanisms for "
			 "embedded systems described in the\n          cryptlib "
			 "manual.\n" );
	unlockPollingMutex();
#else
	externalSourcesPoll( extraEntropy );
#endif /* NO_SYSV_SHAREDMEM */
	}

/* Wait for the randomness gathering to finish */

CHECK_RETVAL \
int waitforRandomCompletion( const BOOLEAN force )
	{
#ifdef NO_SYSV_SHAREDMEM
	return( CRYPT_OK );
#else
	return( externalSourcesPollComplete( force ) );
#endif /* NO_SYSV_SHAREDMEM */
	}

/* Check whether we've forked and we're the child.  The mechanism used varies
   depending on whether we're running in a single-threaded or multithreaded
   environment, for single-threaded we check whether the pid has changed
   since the last check, for multithreaded environments this isn't reliable
   since some systems have per-thread pid's so we need to use
   pthread_atfork() as a trigger to set the pid-changed flag.
   
   This is complicated by the fact that some threads implementations don't 
   call pthread_atfork() on a vfork() (see the note about OS X below) while 
   others do, so that with sufficiently obstreperous use of vfork() (doing 
   stuff other than calling one of the exec() functions) it's possible to 
   end up with duplicate pools.  OTOH this behaviour is explicitly advised 
   against in vfork() manpages and documented as leading to undefined 
   behaviour, so anyone who does this kinda gets what they deserve.

   In terms of OS-specific issues, under Aches calling pthread_atfork() with 
   any combination of arguments or circumstances produces a segfault, so we 
   disable its use and fall back to the getpid()-based fork detection.  In 
   addition some other environments don't support the call, so we exclude 
   those as well.  FreeBSD is a particular pain because of its highly 
   confusing use of -RELEASE, -STABLE, and -CURRENT while maintaining the 
   same version, it's present in 5.x-CURRENT but not 5.x-RELEASE or -STABLE, 
   so we have to exclude it for all 5.x to be safe.  OS X is also a bit of a 
   pain, support was added after 10.4 (Tiger) but OS X uses vfork() 
   internally so the atfork handler doesn't get called because parent and 
   child are still sharing the same address space, so we also rely on the 
   getpid()-based fork detection mechanism */

#if defined( USE_THREADS ) && \
	( defined( _AIX ) || defined( __Android__ ) || defined( _CRAY ) || \
	  defined( __MVS__ ) || defined( _MPRAS ) || defined( __APPLE__ ) || \
	  ( defined( __FreeBSD__ ) && OSVERSION <= 5 ) )
  #define NO_PTHREAD_ATFORK
#endif /* USE_THREADS && OSes without pthread_atfork() */

#if defined( USE_THREADS ) && !defined( NO_PTHREAD_ATFORK )

static BOOLEAN forked = FALSE;
static pthread_mutex_t forkedMutex;

BOOLEAN checkForked( void )
	{
	BOOLEAN hasForked;

	/* Read the forked-t flag in a thread-safe manner */
	pthread_mutex_lock( &forkedMutex );
	hasForked = forked;
	forked = FALSE;
	pthread_mutex_unlock( &forkedMutex );

	return( hasForked );
	}

void setForked( void )
	{
	/* Set the forked-t flag in a thread-safe manner */
	pthread_mutex_lock( &forkedMutex );
	forked = TRUE;
	pthread_mutex_unlock( &forkedMutex );
	}

#else

BOOLEAN checkForked( void )
	{
	static pid_t originalPID = -1;

	/* Set the initial PID if necessary */
	if( originalPID == -1 )
		originalPID = getpid();

	/* If the pid has changed we've forked and we're the child, remember the
	   new pid */
	if( getpid() != originalPID )
		{
		originalPID = getpid();
		return( TRUE );
		}

	return( FALSE );
	}
#endif /* USE_THREADS && !NO_PTHREAD_ATFORK */

/* Initialise and clean up any auxiliary randomness-related objects */

void initRandomPolling( void )
	{
	/* Hardcoding in the Posix function name at this point is safe because 
	   it also works for Solaris threads */
#ifdef USE_THREADS
	pthread_mutex_init( &gathererMutex, NULL );

	/* If it's multithreaded code then we need to ensure that we're 
	   signalled if another thread calls fork().  We set the forked flag 
	   in both the child and the parent to ensure that both sides remix the 
	   pool thoroughly */
  #ifndef NO_PTHREAD_ATFORK
	pthread_mutex_init( &forkedMutex, NULL );
	pthread_atfork( NULL, setForked, setForked );
  #endif /* NO_PTHREAD_ATFORK */
#endif /* USE_THREADS */
	}

void endRandomPolling( void )
	{
#ifdef USE_THREADS
	pthread_mutex_destroy( &gathererMutex );

  #ifndef NO_PTHREAD_ATFORK
	pthread_mutex_destroy( &forkedMutex );
  #endif /* NO_PTHREAD_ATFORK */
#endif /* USE_THREADS */
	}
