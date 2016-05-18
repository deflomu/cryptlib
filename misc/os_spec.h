/****************************************************************************
*																			*
*					  cryptlib OS-Specific Defines Header File 				*
*						Copyright Peter Gutmann 1992-2012					*
*																			*
****************************************************************************/

#ifndef _OSSPEC_DEFINED

#define _OSSPEC_DEFINED

/* To build the static .LIB under Win32, uncomment the following define (this
   it not recommended since the init/shutdown is no longer completely thread-
   safe).  In theory it should be possible to detect the build of a DLL vs.a
   LIB with the _DLL define which is set when the /MD (multithreaded DLL)
   option is used, however VC++ only defines _DLL when /MD is used *and*
   it's linked with the MT DLL runtime.  If it's linked with the statically
   linked runtime, _DLL isn't defined, which would result in the unsafe LIB
   version being built as a DLL */

/* #define STATIC_LIB */

/* os_spec.h performs OS and compiler detection that's used by config.h, so
   this file must be applied before config.h */

#ifdef _CONFIG_DEFINED
  #error "os_spec.h must be included before config.h"
#endif /* _CONFIG_DEFINED */

/****************************************************************************
*																			*
*									OS Detection							*
*																			*
****************************************************************************/

/* Try and figure out if we're running under Windows and Win16/Win32/WinCE.
   We have to jump through all sorts of hoops later on, not helped by the
   fact that the method of detecting Windows at compile time changes with
   different versions of Visual C (it's different for each of VC 2.0, 2.1,
   4.0, and 4.1.  It actually remains the same after 4.1) */

#ifndef __WINDOWS__
  #if defined( _Windows ) || defined( _WINDOWS )
	#define __WINDOWS__
  #endif /* Older Windows compilers */
  #ifdef __MINGW32__
	#define __WINDOWS__
  #endif /* MinGW */
#endif /* Windows */
#if !defined( __WIN32__ ) && ( defined( WIN32 ) || defined( _WIN32 ) )
  #ifndef __WINDOWS__
	#define __WINDOWS__		/* Win32 or WinCE */
  #endif /* __WINDOWS__ */
  #ifdef _WIN32_WCE
	#define __WINCE__
  #else
	#define __WIN32__
  #endif /* WinCE vs. Win32 */
  #if defined( _M_X64 )
	#define __WIN64__
  #endif /* Win64 */
#endif /* Win32 or WinCE */
#if defined( __WINDOWS__ ) && \
	!( defined( __WIN32__ ) || defined( __WINCE__ ) )
  #define __WIN16__
#endif /* Windows without Win32 or WinCE */

/* If we're using a DOS compiler and it's not a 32-bit one, record this.
   __MSDOS__ is predefined by a number of compilers, so we use __MSDOS16__
   for stuff that's 16-bit DOS specific, and __MSDOS32__ for stuff that's
   32-bit DOS specific */

#if defined( __MSDOS__ ) && !defined( __MSDOS32__ )
  #define __MSDOS16__
#endif /* 16-bit DOS */
#if defined( __WATCOMC__ ) && defined( __DOS__ )
  #ifndef __MSDOS__
	#define __MSDOS__
  #endif /* 16- or 32-bit DOS */
  #if defined( __386__ ) && !defined( __MSDOS32__ )
	#define __MSDOS32__
  #endif /* 32-bit DOS */
#endif /* Watcom C under DOS */

/* Make the defines for various OSes look a bit more like the usual ANSI 
  defines that are used to identify the other OS types */

#ifdef __TANDEM
  #if defined( _OSS_TARGET )
	#define __TANDEM_OSS__
  #elif defined( _GUARDIAN_TARGET )
	#define __TANDEM_NSK__
  #else
	#error "Can't determine Tandem OS target type (NSK or OSS)"
  #endif /* Tandem OSS vs. NSK */
#endif /* Tandem */

#if defined( __MWERKS__ ) || defined( SYMANTEC_C ) || defined( __MRC__ )
  #define __MAC__
#endif /* Macintosh */

#if defined( __OS400__ ) || defined( __ILEC400__ )
  #define __AS400__
#endif /* AS/400 */

#ifdef __PALMSOURCE__
  #define __PALMOS__
#endif /* Palm OS */

#ifdef __VMS
  #define __VMS__
#endif /* VMS */

#if defined( __APPLE__ )
  /* Apple provides an environment-specific file that provides detailed
	 information about the target enviroment, defining TARGET_OS_xxx to 1
	 for a given target environment */
  #include <TargetConditionals.h>
  #if TARGET_OS_IPHONE || TARGET_IPHONE_SIMULATOR
	#define __iOS__
  #elif TARGET_OS_WATCH
	/* It's a bit unclear what the OS for Apple's watch will eventually end 
	   up as, for now we treat it as iOS since we're only accessing the low-
	   level functionality */
	#define __iOS__
  #endif /* iOS aliases */
#endif /* __APPLE__ */

/* In some cases we're using a Windows system as an emulated cross-
   development platform, in which case we are we add extra defines to turn 
   off some Windows-specific features.  The override for BOOLEAN is required 
   because once __WIN32__ is turned off we try and typedef BOOLEAN, but 
   under Windows it's already typedef'd which leads to error messages */

#if defined( __WIN32__ ) && ( _MSC_VER == 1200 ) && defined( CROSSCOMPILE )
  /* Embedded OS variant.  Remember to change Project | Settings | C/C++ |
	 Preprocessor | Additional include directories as per the code 
	 comments */
//	#define __ARINC653__	/* Extra include: ./,./embedded/arinc653 */
//	#define __CMSIS__		/* Extra include: ./,./embedded/cmsis */
//  #define __EmbOS__		/* Extra include: ./,./embedded/embos */
//	#define __FreeRTOS__	/* Extra include: ./,./embedded/freertos */
//	#define __ITRON__		/* Extra include: ./,./embedded/itron */
//	#define __Nucleus__		/* Extra include: ./,./embedded/nucleus */
//	#define __RTEMS__		/* Extra include: ./,./embedded/rtems */
//	#define __SMX__			/* Extra include: ./,./embedded/smx/xsmx,./embedded/smx/xfs */
//	#define __ThreadX__		/* Extra include: ./,./embedded/threadx */
//	#define __TKernel__		/* Extra include: ./,./embedded/tk */
//  #define __UCOS__		/* Extra include: ./,./embedded/ucos */
	#define __VxWorks__		/* Extra include: ./,./embedded/vxworks/,./embedded/vxworks/wrn/coreip/ */

  /* Embedded OS additions (filesystems, networking).  Include directory 
     changes as before */
  #define USE_LWIP			/* Extra include: ...,./embedded */
							/* LWIP uses absolute paths, so the 'lwip' in 
							   the path is part of the #include */

  /* Undo Windows defines */
  #undef __WINDOWS__
  #undef __WIN32__
  #if !defined( __Nucleus__ ) && !defined( __SMX__ ) && !defined( __UCOS__ )
	#define BOOLEAN			FNORDIAN
  #endif /* Systems that typedef BOOLEAN */
  #ifdef __Nucleus__
	#undef FAR
  #endif /* Systems that define FAR */

  /* Embedded SDK-specific additional defines */
  #if defined( __VxWorks__ ) && !defined( _WRS_KERNEL )
	#define _WRS_KERNEL		1
  #endif /* SDK-specific defines */

  /* In addition '__i386__' (assuming gcc with an x86 target) needs to be 
     defined globally via Project Settings | C/C++ | Preprocessor.  This
	 is already defined for the 'Crosscompile' build configuration */
#endif /* Windows emulated cross-compile environment */

#ifdef _SCCTK
  #define __IBM4758__
#endif /* IBM 4758 cross-compiled under Windows */

/****************************************************************************
*																			*
*						OS-Specific Compiler Configuration					*
*																			*
****************************************************************************/

/* Visual C++ capabilities have changed somewhat over the years, the 
   following defines make explicit what we're testing for in a check of 
   _MSC_VER.

	Visual C++ 1.5 _MSC_VER = 800
	Visual C++ 2.0 _MSC_VER = 900
	Visual C++ 4.0 _MSC_VER = 1000
	Visual C++ 5.0 _MSC_VER = 1100
	Visual C++ 6.0 _MSC_VER = 1200
	Visual C++ 7.0 (VC++.NET/2002) _MSC_VER = 1300
	Visual C++ 7.1 (VC++.NET/2003) _MSC_VER = 1310
	Visual C++ 8.0 (VC2005) _MSC_VER = 1400 
	Visual C++ 9.0 (VC2008) _MSC_VER = 1500
	Visual C++ 10.0 (VC2010) _MSC_VER = 1600 
	Visual C++ 11.0 (VC2012) _MSC_VER = 1700
	Visual C++ 12.0 (VC2013) _MSC_VER = 1800 
	Visual C++ 14.0 (VC2015) _MSC_VER = 1900 */

#ifdef _MSC_VER
  #define VC_16BIT( version )		( version <= 800 )
  #define VC_LE_VC6( version )		( version <= 1200 )
  #define VC_GE_2002( version )		( version >= 1300 )
  #define VC_LT_2005( version )		( version < 1400 )
  #define VC_GE_2005( version )		( version >= 1400 )
  #define VC_GE_2008( version )		( version >= 1500 )
  #define VC_LT_2010( version )		( version < 1600 )
  #define VC_GE_2010( version )		( version >= 1600 )
  #define VC_GE_2012( version )		( version >= 1700 )
  #define VC_GE_2013( version )		( version >= 1800 )
  #define VC_GE_2015( version )		( version >= 1900 )
#else
  /* These aren't specifically required on non-VC++ systems, but some 
     preprocessors get confused if they aren't defined */
  #define VC_16BIT( version )		0
  #define VC_LE_VC6( version )		0
  #define VC_GE_2002( version )		0
  #define VC_LT_2005( version )		0
  #define VC_GE_2005( version )		0
  #define VC_GE_2008( version )		0
  #define VC_GE_2010( version )		0
  #define VC_GE_2012( version )		0
  #define VC_GE_2013( version )		0
  #define VC_GE_2015( version )		0
#endif /* Visual C++ */

/* If we're compiling under VC++ with the maximum level of warnings, turn
   off some of the more irritating warnings */

#if defined( _MSC_VER )
  #if VC_16BIT( _MSC_VER )
	#pragma warning( disable: 4135 )/* Conversion bet.diff.integral types */
	#pragma warning( disable: 4761 )/* Integral size mismatch in argument */
  #endif /* 16-bit VC++ */

  /* Warning level 3:
  
	 4017: Comparing signed <-> unsigned value.  The compiler has to convert 
		   the signed value to unsigned to perform the comparison.  This 
		   leads to around 25 false-positive warnings.  Note that this is
		   a variant of the VC++ 2005-only warning 4267, this one warns
		   about comparing the result of a sizeof() operation to an int and
		   4267 warns about size_t types in general */
  #pragma warning( disable: 4018 )	/* Comparing signed <-> unsigned value */

  /* Warning level 4:

	 4054, 4055: Cast from function pointer -> generic (data) pointer, cast 
		   from generic (data) pointer -> function pointer.  These are 
		   orthogonal and impossible to disable as they override the 
		   universal 'void *' pointer type.

	 4057: Different types via indirection.  An annoying dual-purpose 
		   warning that leads to huge numbers of false positives for 
		   'char *' vs. 'unsigned char *' (for example due to a PKCS #11 
		   token label, declared as 'unsigned char *', being passed to a 
		   string function, these are pretty much un-fixable as 'char'
		   vs. 'unsigned char's percolate up and down the code tree), 
		   but that also provides useful warnings of potential problems 
		   (for example 'int *' passed to function expecting 'long *').

	 4204, 4221: Struct initialised with non-const value, struct initialised 
		   with address of automatic variable.  Standards extensions that 
		   the struct STATIC_INIT macros manage for us.

	 4206: Empty C module due to #ifdef'd out code.  Annoying noise caused 
		   by empty modules due to disabled functionality.

	 The only useful ones are 4057, which can be turned off on a one-off 
	 basis to identify new true-positive issues before being disabled again 
	 to avoid all of the false-positives, currently 100 for 4057 */
  #pragma warning( disable: 4054 )	/* Cast from fn.ptr -> generic (data) ptr.*/
  #pragma warning( disable: 4055 )	/* Cast from generic (data) ptr. -> fn.ptr.*/
  #pragma warning( disable: 4057 )	/* Different types via indirection */
  #pragma warning( disable: 4204 )	/* Struct initialised with non-const value */
  #pragma warning( disable: 4206 )	/* Empty C module due to #ifdef'd out code */
  #pragma warning( disable: 4221 )	/* Struct initialised with addr.of auto.var */
  #if VC_GE_2005( _MSC_VER )
	#pragma warning( disable: 4267 )/* int <-> size_t */
  #endif /* VC++ 2005 or newer */

  /* Different versions of VC++ generates extra warnings at level 4 due to 
	 problems in VC++/Platform SDK headers */
  #pragma warning( disable: 4201 )/* Nameless struct/union in SQL/networking hdrs*/
  #if VC_GE_2005( _MSC_VER )
	#pragma warning( disable: 4214 )/* bit field types other than int */
  #endif /* VC++ 2005 or newer */

  /* Code analysis generates even more warnings.  C6011 is particularly 
	 problematic, it's issued whenever a pointer is derefenced without first
	 checking that it's not NULL, which makes it more or less unusable */
  #if defined( _MSC_VER ) && defined( _PREFAST_ ) 
	#pragma warning( disable: 6011 )/* Deferencing NULL pointer */
  #endif /* VC++ with source analysis enabled */

  /* Windows DDK free builds treat warnings as errors and the DDK headers 
	 have some problems so we have to disable additional warnings */
  #ifdef WIN_DDK
	#pragma warning( disable: 4242 )/* MS-only bit field type used */
	#pragma warning( disable: 4731 )/* Frame pointer modified by inline asm */
  #endif /* WIN_DDK */

  /* gcc -wall type warnings.  The highest warning level generates large
	 numbers of spurious warnings (including ones in VC++ headers), so it's
	 best to only enable them for one-off test builds requiring manual
	 checking for real errors */
  #pragma warning( disable: 4100 )	/* Unreferenced parameter */
#endif /* Visual C++ */

/* Under VC++/VS a number of warnings are disabled by default, including 
   some potentially useful ones, so we re-enable them.  The warnings are:

	C4242 'identifier': conversion from 'type1' to 'type2', possible loss of 
		  data.
	C4255 'function': no function prototype given: converting '()' to 
		  '(void)'.
	C4287 'operator': unsigned/negative constant mismatch.
	C4296 'operator': expression is always false.
	C4302 'conversion' : truncation from 'type 1' to 'type 2'.
	C4311 'variable' : pointer truncation from 'type' to 'type'.
	C4431 missing type specifier - int assumed.
	C4545 expression before comma evaluates to a function which is missing 
		  an argument list.
	C4546 function call before comma missing argument list.
	C4547 'operator' : operator before comma has no effect; expected 
		  operator with side-effect.
	C4548 expression before comma has no effect; expected expression with 
		  side-effect.
	C4549 'operator' : operator before comma has no effect; did you intend 
		  'operator'?
	C4555 expression has no effect; expected expression with side-effect.
	C4619 #pragma warning : there is no warning number 'number'.
	C4668 'symbol' is not defined as a preprocessor macro, replacing with 
		  '0' for 'directives'.  
		  Note that enabling this check causes warnings in Windows header 
		  files.
	C4826 Conversion from 'type1 ' to 'type2' is sign-extended.

   These are all defined only for newer versions of VC++ (2005 and 2010), so 
   they need a recent compiler in order to be evaluated.

   These versions also have the potentially useful warning 'C4390 empty 
   controlled statement found' (e.g. 'if( i );'), on by default for W3 and 
   above, however this warning has no effect in either VS 2005 or VS 2010,
   it seems to be triggered by random misplaced semicolons rather than the
   presence of empty controlled statements, e.g. 'if( foo; )' */

#if defined( _MSC_VER )
  #pragma warning( 3: 4242 )
  #pragma warning( 3: 4255 )
  #pragma warning( 3: 4287 )
  #pragma warning( 3: 4302 )
  #pragma warning( 3: 4311 )
  #pragma warning( 3: 4296 )
  #pragma warning( 3: 4431 )
  #pragma warning( 3: 4545 )
  #pragma warning( 3: 4546 )
  #pragma warning( 3: 4547 )
  #pragma warning( 3: 4548 )
  #pragma warning( 3: 4549 )
  #pragma warning( 3: 4555 )
  #pragma warning( 3: 4619 )
  #pragma warning( 3: 4668 )
  #pragma warning( 3: 4826 )
#endif /* Visual C++ */

/* VC++ 2005 implements the TR 24731 security extensions but doesn't yet 
   define __STDC_LIB_EXT1__, so if we detect this version of the compiler we 
   define it ourselves */

#if defined( _MSC_VER ) && VC_GE_2005( _MSC_VER ) && \
	!defined( __STDC_LIB_EXT1__ )
  #define __STDC_LIB_EXT1__
#endif /* VC++ 2005 without __STDC_LIB_EXT1__ defined */

/* The ability to modify warnings via the project file in BC++ 5.0x is
   completely broken, the only way to do this is via pragmas in the source
   code */

#if defined( __BORLANDC__ ) && ( __BORLANDC__ < 0x550 )
  /* Spurious warnings to disable */
  #pragma warn -aus						/* Assigned but never used.  This is
										   frequently misreported even when
										   the value is quite obviously used */
  #pragma warn -csu						/* Comparing signed/unsigned value */
  #pragma warn -par						/* Parameter is never used	*/
  #pragma warn -sig						/* Conversion may lose significant digits */
  #pragma warn -ucp						/* Signed/unsigned char assignment */

  /* Useful warnings to enable */
  #pragma warn +amb						/* Ambiguous operators need parentheses */
  #pragma warn +amp						/* Superfluous & with function */
  #pragma warn +asm						/* Unknown assembler instruction */
  #pragma warn +ccc						/* Condition is always true/false */
  #pragma warn +cln						/* Constant is long */
  #pragma warn +def						/* Use of ident before definition */
  #pragma warn +stv						/* Structure passed by value */
#endif /* Broken BC++ 5.0x warning handling */

/* The TI compiler needs to have a few annoying warnings disabled */

#if defined( __TI_COMPILER_VERSION__ )
  #pragma diag_suppress 190				/* enum vs. int */
#endif /* TI compiler */

/* All Windows CE functions are Unicode-only, this was an attempt to clean
   up the ASCII vs. Unicode kludges in Win32 but unfortunately was made just
   before UTF8 took off.  Because UTF8 allows everyone to keep using their
   old ASCII stuff while being nominally Unicode-aware, it's unlikely that
   any new Unicode-only systems will appear in the future, leaving WinCE's
   Unicode-only API an orphan.  The easiest way to handle this is to convert
   all strings to ASCII/8 bit as they come in from the external cryptlib API
   and convert them back to Unicode as required when they're passed to WinCE
   OS functions.  In other words Unicode is treated just like EBCDIC and
   pushed out to the edges of cryptlib.  This requires the minimum amount of
   conversion and special-case handling internally */

#ifdef __WINCE__
  #define UNICODE_CHARS
#endif /* WinCE */

/* Include stdint.h if it's available, since this greatly simplifies the
   handling of data types in a portable manner */

#if defined( __STDC_VERSION__ ) && ( __STDC_VERSION__ >= 199901L ) 
  /* stdint.h via C99 compatibility */
  #include <stdint.h>
#elif defined( __GNUC__ ) && ( __GNUC__ > 3 ) 
  /* stdint.h via GNU headers */
  #include <stdint.h>
#elif defined( _MSC_VER ) && VC_GE_2015( _MSC_VER )
  /* stdint.h via Visual Studio */
  #include <stdint.h>
#elif defined( _MSC_VER )
  #ifdef __WIN64__
	typedef unsigned __int64	uintptr_t;
  #else
	typedef unsigned long		uintptr_t;
  #endif /* 64- vs 32-bit systems */
#else
  #if ULONG_MAX > 0xFFFFFFFFUL
	typedef unsigned long long	uintptr_t;
  #else
	typedef unsigned long		uintptr_t;
  #endif /* 64- vs 32-bit systems */
#endif /* Various stdint.h options */

/* If we're compiling on the AS/400, make enums a fixed size rather than
   using the variable-length values that IBM compilers default to, and force
   strings into a read-only segment (by default they're writeable) */

#ifdef __AS400__
  #pragma enumsize( 4 )
  #pragma strings( readonly )
  #define EBCDIC_CHARS
#endif /* AS/400 */

/* If we're compiling under MVS or VM/CMS, make enums a fixed size rather
   than using the variable-length values that IBM compilers default to */

#if defined( __MVS__ ) || defined( __VMCMS__ )
  #pragma enum( 4 )
  #define USE_ETOA		/* Use built-in ASCII <-> EBCDIC conversion */
  #define EBCDIC_CHARS
#endif /* __MVS__ */

/* If we're compiling under QNX, make enums a fixed size rather than using
   the variable-length values that the Watcom compiler defaults to */

#if defined( __QNX__ ) && defined( __WATCOMC__ )
  #pragma enum int
#endif /* QNX and Watcom C */

/* Symbian has rather inconsistent defines depending in which toolchain 
   we're using, with the original ARM tools the define was __SYMBIAN32__
   with __MARM__ for the ARM architecture, with the ex-Metrowerks Nokia
   compiler the define is __EMU_SYMBIAN_OS__ for the emulated environment
   and who knows what for the gcc toolchain.  To make checking easier we
   require __SYMBIAN32__ for all environments, with __MARM__ vs.
   __EMU_SYMBIAN_OS__ distinguishing between ARM and x86 emulator */

#if defined( __EMU_SYMBIAN_OS__ ) && !defined( __SYMBIAN32__ )
  #error Need to define '__SYMBIAN32__' for the Symbian build
#endif /* __EMU_SYMBIAN_OS__ && !__SYMBIAN32__ */
#if defined( __SYMBIAN32__ ) && \
	!( defined( __MARM__ ) || defined( __EMU_SYMBIAN_OS__ ) )
  #error Need to define a Symbian target architecture type, e.g. ARM or x86
#endif /* __SYMBIAN32__ && !( __MARM__ || __EMU_SYMBIAN_OS__ ) */

/* A few rare operations are word-size-dependant */

#if INT_MAX <= 32768L
  #define SYSTEM_16BIT
#elif ULONG_MAX > 0xFFFFFFFFUL
  #define SYSTEM_64BIT
#else
  #define SYSTEM_32BIT
#endif /* 16- vs.32- vs.64-bit system */

/* Useful data types.  Newer compilers provide a 'bool' datatype via 
   stdbool.h, but in a fit of braindamage generally make this a char instead 
   of an int.  While Microsoft's use of char for BOOLEAN in the early 1980s 
   with 8/16-bit 8086s and 129K of RAM makes sense, it's a pretty stupid 
   choice for 32- or 64-bit CPUs because alignment issues mean that it'll 
   generally still require 32 or 64 bits of storage (except for special 
   cases like an array of bool), but then the difficulty or even inability 
   of many CPUs and/or architectures in performing byte-level accesses means 
   that in order to update a boolean the system has to fetch a full machine 
   word, mask out the byte data, or/and in the value, and write the word 
   back out.  So 'bool' = 'char' combines most of the worst features of both 
   char and int.  It also leads to really hard-to-find implementation bugs 
   due to the fact that '(bool) int = true' produces different results to 
   '*(bool *) intptr = true', something that was resolved years ago in enums 
   without causing such breakage.

   Because of this we avoid the use of bool and just define it to int */

typedef unsigned char		BYTE;
#if defined( __STDC_VERSION__ ) && ( __STDC_VERSION__ >= 199901L ) && 0
  #include <stdbool.h>
  typedef bool              BOOLEAN;
#elif defined( __WIN32__ ) || defined( __WINCE__ )
  /* VC++ typedefs BOOLEAN so we need to use the preprocessor to override it */
  #define BOOLEAN			int
#elif defined( __UCOS__ ) || defined( __SMX__ )
  /* Some OSes typedef BOOLEAN themselves so we set it as a #define, which 
	 means that we can then work around the typedef by undefining and
	 redefining it around the include of the OS-specific headers:

		#undef BOOLEAN
		#include <smx.h>
		#define BOOLEAN int */
  #if defined( __SMX__ ) && !defined( _MSC_VER )
	typedef int				BOOLEAN
  #else
	#define BOOLEAN			int
  #endif /* OS-specific BOOLEAN juggling */
#elif defined( __Nucleus__ )
  /* Nucleus defines BOOLEAN as 'unsigned char' so we override it to be an
     int */
  #undef  BOOLEAN
  #define BOOLEAN			int
#else
  typedef int				BOOLEAN;
#endif /* Boolean data type on different platforms */

/* If we're building the Win32 kernel driver version, include the DDK
   headers */

#if defined( __WIN32__ ) && defined( NT_DRIVER )
  #include <ntddk.h>
#endif /* NT kernel driver */

/* In 16-bit environments the BSS data is large enough that it overflows the 
   (64K) BSS segment.  Because of this we move as much of it as possible 
   into its own segment with the following define */

#if defined( __WIN16__ )
  #ifdef _MSC_VER
	#define FAR_BSS	__far
  #else
	#define FAR_BSS	far
  #endif /* VC++ vs.other compilers */
#else
  #define FAR_BSS
#endif /* 16-bit systems */

/* If we're using eCOS, include the system config file that tells us which 
   parts of the eCOS kernel are available */

#ifdef __ECOS__
  #include <pkgconf/system.h>
#endif /* __ECOS__ */

/* The VxWorks SDK defines the value 'SH' (to indicate the use of SuperH 
   CPU family) in vxCpu.h which conflicts with the 'struct SH' in ssh.h. 
   To fix this we undefine it, this shouldn't be a problem since the define 
   SH32 is set to the same value as SH and presumably no-one will be using 
   the basic 20-year-old SuperH any more.

   VxWorks also uses some global symbols that clash with cryptlib's ones, 
   to resolve this we redefine the cryptlib ones to have a 'cl_' prefix */

#ifdef __VxWorks__
  /* Correct the use of the VxWorks preprocessor define 'SH' overriding 
     'struct SH' in ssh.h */
  #if defined( SH )
	#undef SH
  #endif /* SH */

  /* Correct clashing global symbols in VxWorks */
  #define setSerialNumber		cl_setSerialNumber
  #define inflate				cl_inflate
  #define addAction				cl_addAction
  #define inflate_copyright		cl_inflate_copyright
  #define zlibVersion			cl_zlibVersion
#endif /* __VxWorks__ */

/* Some versions of the WinCE SDK define 'interface' as part of a complex 
   series of kludges for OLE support (made even more amusing by the fact 
   that 'interface' is an optional keyword in eVC++ which may or may not 
   be recognised as such by the compiler), to avoid conflicts we undefine 
   it if it's defined since we're not using any OLE functionality */

#if defined( __WINCE__ ) && defined( interface )
  #undef interface
#endif /* WinCE SDK */

/* Some systems (typically 16-bit or embedded ones) have rather limited
   amounts of memory available, if we're building on one of these we limit
   the size of some of the buffers that we use and the size of the object
   table */

#if defined( __MSDOS16__ ) || defined( __uClinux__ )
  #define CONFIG_CONSERVE_MEMORY
  #define CONFIG_NUM_OBJECTS		128
#endif /* Memory-starved systems */

/* Since the Win32 randomness-gathering uses a background randomness polling
   thread, we can't build a Win32 version with NO_THREADS */

#if defined( __WIN32__ ) && defined( NO_THREADS )
  #error The Win32 version of cryptlib must have threading enabled
#endif /* Win32 without threading */

/* Boolean constants */

#ifndef TRUE
  #define FALSE			0
  #define TRUE			!FALSE
#endif /* Boolean values */

/* cryptlib contains a few locations that require forward declarations for
   static data:

	extern const int foo[];

	foo[ i ] = bar;

	static const int foo[] = { ... };

   Compiler opinions on how to handle this vary.  Some compile it as is
   (i.e. 'static const ...'), some don't allow the 'static', some allow both
   variants, and some produce warnings with both but allow them anyway
   (there are probably more variants with further compilers).  To get around
   this, we use the following define and then vary it for broken compilers
   (the following is the minimum required to get it to compile, other broken
   compilers will still produce warnings) */

#if ( defined( __BORLANDC__ ) && ( __BORLANDC__ < 0x550 ) ) || \
	defined( __VMCMS__ ) || defined( __MVS__ ) || defined( __MRC__ ) || \
	defined( __TANDEM_NSK__ ) || defined( __TANDEM_OSS__ ) || \
	( defined( __UNIX__ ) && ( defined( __HP_cc ) || defined( __HP_aCC ) ) ) || \
	( defined( __UNIX__ ) && defined( _MPRAS ) )
  #define STATIC_DATA
#else
  #define STATIC_DATA	static
#endif /* Fn.prototyping workarounds for borken compilers */

/* A few compilers won't allow initialisation of a struct at runtime, so
   we have to kludge the init with macros.  This is rather ugly since
   instead of saying "struct = { a, b, c }" we have to set each field
   individually by name.  The real reason for doing this though is that
   if the compiler can initialise the struct directly, we can make the
   fields const for better usage checking by the compiler.

   There are two forms of this, one for simple structs and one for arrays
   of structs.  At the moment the only use for the array-init is for the
   situation where the array represents a sequence of search options with
   the last one being a terminator entry, so we provide a simplified form
   that only sets the required fields.
   
   The value of __SUNPRO_C bears no relation whatsoever to the actual 
   version number of the compiler and even Sun's docs give different values 
   in different places for the same compiler version, but 0x570 seems to 
   work */

#if ( defined( __BORLANDC__ ) && ( __BORLANDC__ < 0x550 ) ) || \
	defined( _CRAY ) || \
	( defined( __hpux ) && !defined( __GNUC__ ) ) || \
	( defined( __QNX__ ) && ( OSVERSION <= 4 ) ) || \
	defined( __RVCT2_1__ ) || \
	( defined( __SUNPRO_C ) && ( __SUNPRO_C <= 0x570 ) ) || \
	defined( __SCO_VERSION__ ) || defined(  __TANDEM )
  #define CONST_INIT
  #define CONST_INIT_STRUCT_3( decl, init1, init2, init3 ) \
		  decl
  #define CONST_INIT_STRUCT_4( decl, init1, init2, init3, init4 ) \
		  decl
  #define CONST_INIT_STRUCT_5( decl, init1, init2, init3, init4, init5 ) \
		  decl
  #define CONST_SET_STRUCT( init ) \
		  init

  #define CONST_INIT_STRUCT_A2( decl, init1, init2 ) \
		  decl
  #define CONST_SET_STRUCT_A( init ) \
		  init
#else
  #define CONST_INIT	const
  #define CONST_INIT_STRUCT_3( decl, init1, init2, init3 ) \
		  decl = { init1, init2, init3 }
  #define CONST_INIT_STRUCT_4( decl, init1, init2, init3, init4 ) \
		  decl = { init1, init2, init3, init4 }
  #define CONST_INIT_STRUCT_5( decl, init1, init2, init3, init4, init5 ) \
		  decl = { init1, init2, init3, init4, init5 }
  #define CONST_SET_STRUCT( init )

  #define CONST_INIT_STRUCT_A2( decl, init1, init2 ) \
		  const decl = { { init1, 0 }, { init2, 0 } }
  #define CONST_SET_STRUCT_A( init )
#endif /* Watcom C || SunPro C || SCO C */

/* The Tandem mktime() is broken and can't convert dates beyond 2023, so we
   replace it with our own version which can */

#if defined( __TANDEM_NSK__ ) || defined( __TANDEM_OSS__ )
  #define mktime	my_mktime
#endif /* __TANDEM_NSK__ || __TANDEM_OSS__ */

/* Enable use of assembly-language alternatives to C functions if possible.
   Note that the following asm defines are duplicated in crypt/osconfig.h,
   because the OpenSSL headers are non-orthogonal to the cryptlib ones.  Any 
   changes made here need to be reflected in osconfig.h */

#if defined( __WIN32__ ) && \
	!( defined( __WIN64__ ) || defined( __BORLANDC__ ) || defined( NO_ASM ) )
  /* Enable use of the AES ASM code */
  #define AES_ASM

  /* Enable use of zlib ASM longest-match and decompression code.  Assemble
     with "ml /Zp /coff /c gvmat32.asm" and "yasm -f win32 inffas32y.asm" */
  #define ASMV
  #define ASMINF
#endif /* Win32 */

/* Alongside the general crypto asm code there's also inline asm to handle 
   things like CPU hardware features, if we're running under Win64 we have 
   to disable this as well */

#if defined( __WIN64__ )
  #define NO_ASM
#endif /* Win64 */

/* In some environments va_list is a scalar, so it can't be compared with 
   NULL in order to verify its validity.  This was particularly problematic 
   with the ARM ABI, which changed the type in late 2009 to 
   'struct __va_list { void *__ap; }', breaking compatibility with all 
   existing code.  We can detect this by taking advantage of the fact that 
   support for the change was added in gcc 4.4, so any newer version with 
   ARM_EABI defined will have a scalar va_list.
   
   Super-H variants also have scalar va_lists, the Super-H varargs header 
   va-sh.h uses a complex structure to handle va_lists for all SH3 and SH4 
   variants, this presumably extends to SH5 as well so we treat va_lists on 
   Super-H as scalars */

#if defined( __GNUC__ )
  #if( defined( __ARM_EABI__ ) && \
	   ( __GNUC__ == 4 && __GNUC_MINOR__ >= 4 ) || ( __GNUC__ > 4 ) )
	/* In theory we could check __ap but in practice it's too risky to rely 
	   on the type and state of hidden internal fields, and in any case it's 
	   only a sanity check, not a hard requirement, so we just no-op the 
	   check out */
	#define verifyVAList( x ) TRUE
  #elif defined( __sh__ )
	#define verifyVAList( x ) TRUE
  #endif /* Architecture-specific scalar va_lists */
#elif defined( __RVCT2_1__ ) || defined( __IAR_SYSTEMS_ICC__ )
  /* The RealView and IAR compilers have the same issue */
  #define verifyVAList( x ) TRUE
#endif /* Nonstandard va_list types */
#ifndef verifyVAList
  #define verifyVAList( x ) ( ( x ) != NULL )
#endif /* Verify function for vector arg lists */

/* cryptlib has many code sequences of the form:

	status = foo();
	if( cryptStatusOK( status ) )
		status = bar();
	if( cryptStatusOK( status ) )
		status = baz();
	if( cryptStatusOK( status ) )
		...

   These can be made more efficient when the compiler can assume that the
   majority case has 'status == CRYPT_OK'.  gcc provides a means of doing 
   this via __builtin_expect().  As usual for gcc the documentation for this 
   is quite confusing:

     "if( __builtin_expect( x, 0 ) ) foo (); would indicate that we do not 
	 expect to call foo, since we expect x to be zero"

   In this case the test is actually the expression 'x', which is evaluated
   as 'x != 0', with the second parameter only taking values 0 (to mean 'not
   likely') or 1 (to mean 'likely').  So the appropriate usage is 
   "__builtin_expect( expr, 0 )" to mean that we don't expect something and 
   "__builtin_expect( expr, 1 )" to mean that we do expect it.  The 
   following forms of cryptStatusError() and cryptStatusOK() assume that in 
   the majority of situations we won't encounter the error case */

#if defined( __GNUC__ ) && ( __GNUC__ >= 3 )
  #undef cryptStatusError
  #undef cryptStatusOK
  #define cryptStatusError( status ) \
		  __builtin_expect( ( status ) < CRYPT_OK, 0 )
  #define cryptStatusOK( status ) \
		  __builtin_expect( ( status ) == CRYPT_OK, 1 )
#endif /* gcc 3.x and newer */

/* Nucleus has it's own functions for allocating and freeing memory, so
   we provide wrappers for them that override the default clAlloc()/clFree()
   mappings */

#ifdef __Nucleus__ 
  #define clAlloc( string, size )		clAllocFn( size )
  #define clFree( string, memblock )	clFreeFn( memblock )
  void *clAllocFn( size_t size );
  void clFreeFn( void *memblock );
#endif /* __Nucleus__ */

/****************************************************************************
*																			*
*								Dynamic Loading Support						*
*																			*
****************************************************************************/

/* On systems that support dynamic loading, we bind various drivers and
   libraries at runtime rather than at compile time.  Under Windows this is
   fairly easy but under Unix it's supported somewhat selectively and may be
   buggy or platform-specific */

#if defined( __WINDOWS__ ) || \
	( defined( __UNIX__ ) && \
	  ( ( defined( sun ) && OSVERSION > 4 ) || defined( __linux__ ) || \
		defined( _AIX ) || ( defined( __APPLE__ ) && !defined( __MAC__ ) ) ) ) || \
	defined( __ANDROID__ )
  #define DYNAMIC_LOAD

  /* Macros to map OS-specific dynamic-load values to generic ones */
  #if defined( __WINDOWS__ )
	#define INSTANCE_HANDLE		HINSTANCE
	#define NULL_INSTANCE		( HINSTANCE ) NULL
	#ifdef __WINCE__
	  #define DynamicLoad( name ) LoadLibrary( name )
	#else
	  #define DynamicLoad( name ) SafeLoadLibrary( name )
	#endif /* Win32 vs. WinCE */
	#define DynamicUnload		FreeLibrary
	#define DynamicBind			GetProcAddress
  #elif defined( __UNIX__ ) || defined( __ANDROID__ )
    /* Older versions of OS X didn't have dlopen() support but required
	   the use of the rather painful low-level dyld() interface.  If you're
	   running an older version of OS X and don't have the dlcompat wrapper
	   installed, get Peter O'Gorman's dlopen() implementation, which wraps
	   the dyld() interface */
	#include <dlfcn.h>
	#define INSTANCE_HANDLE		void *
	#define NULL_INSTANCE		NULL
	#define DynamicLoad( name )	dlopen( name, RTLD_LAZY )
	#define DynamicUnload		dlclose
	#define DynamicBind			dlsym
  #elif defined __VMCMS__
	#include <dll.h>

	#define INSTANCE_HANDLE		dllhandle *
	#define NULL_INSTANCE		NULL
	#define DynamicLoad( name )	dllload( name, RTLD_LAZY )
	#define DynamicUnload		dllfree
	#define DynamicBind			dlqueryfn
  #endif /* OS-specific instance handles */
#endif /* Windows || Some Unix versions */

/****************************************************************************
*																			*
*								Endianness Defines							*
*																			*
****************************************************************************/

/* If the endianness isn't predefined and the compiler can tell us what
   endianness we've got, use this in preference to all other methods.  This
   is only really necessary on non-Unix systems since the makefile runtime
   test will tell us the endianness under Unix */

#if defined( CONFIG_DATA_LITTLEENDIAN ) || defined( CONFIG_DATA_BIGENDIAN )
  /* If we're cross-compiling for another system, the endianness auto-
	 detection will have been overridden.  In this case we force it to be
	 what the user has specified rather than what we've auto-detected */
  #undef DATA_LITTLEENDIAN
  #undef DATA_BIGENDIAN
  #ifdef CONFIG_DATA_LITTLEENDIAN
	#define DATA_LITTLEENDIAN
  #else
	#define DATA_BIGENDIAN
  #endif /* CONFIG_DATA_LITTLEENDIAN */
#endif /* Forced big vs.little-endian */

#if !defined( DATA_LITTLEENDIAN ) && !defined( DATA_BIGENDIAN )
  #if defined( BIG_ENDIAN ) && defined( LITTLE_ENDIAN ) && defined( BYTE_ORDER )
	/* Some systems define both BIG_ENDIAN and LITTLE_ENDIAN, then define
	   BYTE_ORDER to the appropriate one, so we check this and define the
	   appropriate value */
	#if ( BYTE_ORDER == BIG_ENDIAN ) && !defined( DATA_BIGENDIAN )
	  #define DATA_BIGENDIAN
	#elif ( BYTE_ORDER == LITTLE_ENDIAN ) && !defined( DATA_LITTLEENDIAN )
	  #define DATA_LITTLEENDIAN
	#else
	  #error BYTE_ORDER is neither BIG_ENDIAN nor LITTLE_ENDIAN
	#endif /* BYTE_ORDER-specific define */
  #elif defined( _M_I86 ) || defined( _M_IX86 ) || defined( _M_X64 ) || \
		defined( __TURBOC__ ) || defined( __OS2__ )
	#define DATA_LITTLEENDIAN	/* Intel architecture always little-endian */
  #elif defined( __WINCE__ )
	/* For WinCE it can get a bit complicated, however because of x86 cargo
	   cult programming WinCE systems always tend to be set up in little-
	   endian mode */
	#define DATA_LITTLEENDIAN	/* Intel architecture always little-endian */
  #elif defined( AMIGA ) || defined( __MWERKS__ ) || defined( SYMANTEC_C ) || \
		defined( THINK_C ) || defined( applec ) || defined( __MRC__ )
	#define DATA_BIGENDIAN		/* Motorola architecture always big-endian */
  #elif defined( VMS ) || defined( __VMS )
	#define DATA_LITTLEENDIAN	/* VAX architecture always little-endian */
  #elif defined( __TANDEM_NSK__ ) || defined( __TANDEM_OSS__ )
	#define DATA_BIGENDIAN		/* Tandem architecture always big-endian */
  #elif defined( __AS400__ ) || defined( __VMCMS__ ) || defined( __MVS__ )
	#define DATA_BIGENDIAN		/* IBM big iron always big-endian */
  #elif defined( __SYMBIAN32__ ) && \
		( defined( __MARM__ ) || defined( __EMU_SYMBIAN_OS__ ) )
	#define DATA_LITTLEENDIAN	/* Symbian on ARM/x86 always little-endian */
  #elif defined( __Nucleus__ ) && defined( __RVCT2_1__ )
	#if defined( __BIG_ENDIAN )	/* Realview for Nucleus */
	  #define DATA_BIGENDIAN
	#else
	  #define DATA_LITTLEENDIAN
	#endif /* Big vs.little-endian */
  #elif defined( __m68k__  )
	#define DATA_BIGENDIAN		/* 68K always big-endian */
  #elif defined( __TI_COMPILER_VERSION__ )
	/* The TI compiler can masquerade as gcc so we need to check for it 
	   before we check for Gnu indicators */
	#if CPU_BYTE_ORDER == LOW_BYTE_FIRST
	  #define DATA_LITTLEENDIAN
	#elif CPU_BYTE_ORDER == HIGH_BYTE_FIRST
	  #define DATA_BIGENDIAN
	#else
	  #error Couldnt get endianness from CPU_BYTE_ORDER
	#endif /* TI compiler endianness detection */
  #elif defined __GNUC__
	#ifdef BYTES_BIG_ENDIAN
	  #define DATA_BIGENDIAN	/* Big-endian byte order */
	#else
	  #define DATA_LITTLEENDIAN	/* Undefined = little-endian byte order */
	#endif /* __GNUC__ */
  #endif /* Compiler-specific endianness checks */
#endif /* !( DATA_LITTLEENDIAN || DATA_BIGENDIAN ) */

/* The last-resort method.  Thanks to Shawn Clifford
   <sysop@robot.nuceng.ufl.edu> for this trick.

   NB: A number of compilers aren't tough enough for this test */

#if !defined( DATA_LITTLEENDIAN ) && !defined( DATA_BIGENDIAN )
  #if ( ( ( unsigned short ) ( 'AB' ) >> 8 ) == 'B' )
	#define DATA_LITTLEENDIAN
  #elif ( ( ( unsigned short ) ( 'AB' ) >> 8 ) == 'A' )
	#define DATA_BIGENDIAN
  #else
	#error "Cannot determine processor endianness - edit misc/os_spec.h and recompile"
  #endif /* Endianness test */
#endif /* !( DATA_LITTLEENDIAN || DATA_BIGENDIAN ) */

/* Sanity check to catch both values being defined */

#if defined( DATA_LITTLEENDIAN ) && defined( DATA_BIGENDIAN )
  #error Both DATA_LITTLEENDIAN and DATA_BIGENDIAN are defined
#endif /* DATA_LITTLEENDIAN && DATA_BIGENDIAN */

/****************************************************************************
*																			*
*								Filesystem Values							*
*																			*
****************************************************************************/

/* When performing file I/O we need to know how large path names can get in
   order to perform range checking and allocate buffers.  This gets a bit
   tricky since not all systems have PATH_MAX, so we first try for PATH_MAX,
   if that fails we try _POSIX_PATH_MAX (which is a generic 255 bytes and if
   defined always seems to be less than whatever the real PATH_MAX should be),
   if that also fails we grab stdio.h and try and get FILENAME_MAX, with an
   extra check for PATH_MAX in case it's defined in stdio.h instead of
   limits.h where it should be.  FILENAME_MAX isn't really correct since it's
   the maximum length of a filename rather than a path, but some environments
   treat it as if it were PATH_MAX and in any case it's the best that we can
   do in the absence of anything better */

#if defined( PATH_MAX )
  #define MAX_PATH_LENGTH		PATH_MAX
#elif defined( _POSIX_PATH_MAX )
  #define MAX_PATH_LENGTH		_POSIX_PATH_MAX
#elif defined( __FileX__ )
  #define MAX_PATH_LENGTH		FX_MAXIMUM_PATH
#else
  #ifndef FILENAME_MAX
	#include <stdio.h>
  #endif /* FILENAME_MAX */
  #if defined( PATH_MAX )
	#define MAX_PATH_LENGTH		PATH_MAX
  #elif defined( MAX_PATH )
	#define MAX_PATH_LENGTH		MAX_PATH
  #elif defined( FILENAME_MAX )
	#define MAX_PATH_LENGTH		FILENAME_MAX
  #elif defined( __MSDOS16__ )
	#define FILENAME_MAX	80
  #else
	#error Need to add a MAX_PATH_LENGTH define in misc/os_spec.h
  #endif /* PATH_MAX, MAX_PATH, or FILENAME_MAX */
#endif /* PATH_MAX */
#if MAX_PATH_LENGTH <= 32
  #error MAX_PATH_LENGTH is <= 32 characters, check your build environment
#endif /* Too-short MAX_PATH values */

/* SunOS 4 doesn't have memmove(), but Solaris does, so we define memmove()
   to bcopy() under 4.  In addition SunOS doesn't define the fseek()
   position indicators so we define these as well */

#if defined( __UNIX__ ) && defined( sun ) && ( OSVERSION == 4 )
  #define memmove				bcopy

  #define SEEK_SET				0
  #define SEEK_CUR				1
  #define SEEK_END				2
#endif /* SunOS 4 */

/****************************************************************************
*																			*
*									Charset Support							*
*																			*
****************************************************************************/

/* Widechar handling.  Most systems now support this, the only support that
   we require is the wchar_t type define.

   Unfortunately in order to check for explicitly enabled widechar support
   via config.h we have to include config.h at this point, because this
   file, containing OS- and compiler-specific settings, both detects the
   OSes and compilers that support widechars in the "OS Detection" section
   above, and then sets the appropriate widechar settings here.  In between
   the two, config.h uses the OS/compiler-detection output to enable or
   disable widechars as required, so we need to slip it in between the two
   sections */

#if defined( INC_ALL )
  #include "config.h"
#else
  #include "misc/config.h"
#endif /* Compiler-specific includes */

#ifdef USE_WIDECHARS
  #if !( defined( __ECOS__ ) || \
		 ( defined( __QNX__ ) && ( OSVERSION <= 4 ) ) || \
		 ( defined( __WIN32__ ) && defined( __BORLANDC__ ) ) || \
		 ( defined( __WINCE__ ) && _WIN32_WCE < 400 ) || \
		 defined( __XMK__ ) )
	#include <wchar.h>
  #endif /* Systems with widechar support in stdlib.h */
#else
  /* No native widechar support, define the necesary types ourselves unless
	 we're running under older OS X (Darwin 6.x), which defines wchar_t in
	 stdlib.h even though there's no wchar support present, or PalmOS, which
	 defines it in wchar.h but then defines it differently in stddef.h, and
	 in any case has no wchar support present */
  #if !( defined( __APPLE__ ) || defined( __MVS__ ) || \
		 defined( __OpenBSD__ ) || defined( __PALMOS__ ) || \
		 defined( __SMX__ ) )
	typedef unsigned short int wchar_t;
  #endif /* __APPLE__ */
#endif /* USE_WIDECHARS */
#define WCSIZE					( sizeof( wchar_t ) )
#ifndef WCHAR_MAX
  #define WCHAR_MAX				( ( wchar_t ) -1 )
#endif /* !WCHAR_MAX */

/* The EOL convention used when outputting text.  Technically speaking 
   Nucleus, SMX, and XMK don't use any particular EOL convention, but since 
   the typical development environment is debug output sent to a Windows 
   terminal emulator, we use CRLF */

#if defined( __MSDOS16__ ) || defined( __MSDOS32__ ) || \
	defined( __Nucleus__ ) || defined( __OS2__ ) || \
	defined( __SMX__ ) || defined( __SYMBIAN32__ ) || \
	defined( __WINDOWS__ ) || defined( __XMK__ )
  #define EOL					"\r\n"
  #define EOL_LEN				2
#elif ( defined( __APPLE__ ) && !defined( __MAC__ ) ) || \
	  defined( __BEOS__ ) || defined( __IBM4758__ ) || \
	  defined( __MVS__ ) || defined( __PALMOS__ ) || \
	  defined( __TANDEM_NSK__ ) || defined( __TANDEM_OSS__ ) || \
	  defined( __UNIX__ ) || defined( __VMCMS__ )
  #define EOL					"\n"
  #define EOL_LEN				1
#elif defined( __MAC__ )
  #define EOL					"\r"
  #define EOL_LEN				1
#elif defined( USE_EMBEDDED_OS )
  /* For embedded OSes we assume a generic Unix-like text environment, these 
	 aren't exactly used for interactive operations like text editing so 
	 there's usually no fixed text format, and many will handle both CRLF 
	 and LF-only text, with the lowest common denominator being the Unix-
	 style LF-only */
  #define EOL					"\n"
  #define EOL_LEN				1
#else
  #error "You need to add the OS-specific define to enable end-of-line handling"
#endif /* OS-specific EOL markers */

/* If we're compiling on IBM mainframes, enable EBCDIC <-> ASCII string
   conversion.  Since cryptlib uses ASCII internally for all strings, we
   need to check to make sure it's been built with ASCII strings enabled
   before we go any further */

#ifdef EBCDIC_CHARS
  #if 'A' != 0x41
	#error cryptlib must be compiled with ASCII literals
  #endif /* Check for use of ASCII */

  int asciiToEbcdic( char *dest, const char *src, const int length );
  int ebcdicToAscii( char *dest, const char *src, const int length );
  char *bufferToEbcdic( char *buffer, const char *string );
  char *bufferToAscii( char *buffer, const char *string );
#endif /* IBM mainframes */

/* If we're compiling on Windows CE, enable Unicode <-> ASCII string
   conversion */

#ifdef UNICODE_CHARS
  int asciiToUnicode( wchar_t *dest, const int destMaxLen, 
					  const char *src, const int length );
  int unicodeToAscii( char *dest, const int destMaxLen, 
					  const wchar_t *src, const int length );
#endif /* Windows CE */

/* Since cryptlib uses ASCII internally, we have to force the use of
   ASCII-compatible versions of system library functions if the system
   uses EBCDIC */

#ifdef EBCDIC_CHARS
  #define ASCII_ALPHA			0x01
  #define ASCII_LOWER			0x02
  #define ASCII_NUMERIC			0x04
  #define ASCII_SPACE			0x08
  #define ASCII_UPPER			0x10
  #define ASCII_HEX				0x20
  extern const BYTE asciiCtypeTbl[];

  #define isAlnum( ch ) \
		  ( asciiCtypeTbl[ byteToInt( ch ) ] & ( ASCII_ALPHA | ASCII_NUMERIC ) )
  #define isAlpha( ch ) \
		  ( asciiCtypeTbl[ byteToInt( ch ) ] & ASCII_ALPHA )
  #define isDigit( ch ) \
		  ( asciiCtypeTbl[ byteToInt( ch ) ] & ASCII_NUMERIC )
  #define isPrint( ch ) \
		  ( ( byteToInt( ch ) ) >= 0x20 && ( byteToInt( ch ) ) <= 0x7E )
  #define isXDigit( ch ) \
		  ( asciiCtypeTbl[ byteToInt( ch ) ] & ASCII_HEX )
  #define toLower( ch ) \
		  ( ( asciiCtypeTbl[ byteToInt( ch ) ] & ASCII_UPPER ) ? \
			( byteToInt( ch ) ) + 32 : ( byteToInt( ch ) ) )
  #define toUpper( ch ) \
		  ( ( asciiCtypeTbl[ byteToInt( ch ) ] & ASCII_LOWER ) ? \
			( byteToInt( ch ) ) - 32 : ( byteToInt( ch ) ) )
  int strCompareZ( const char *src, const char *dest );
  int strCompare( const char *src, const char *dest, int length );
  #define sprintf_s				sPrintf_s
  #define vsprintf_s			sPrintf_s
#else
  #if defined( __Nucleus__ )
	#include <nu_ctype.h>
	#include <nu_string.h>
  #else
	#include <ctype.h>
  #endif /* OS-specific includes */

  #define isAlnum( ch )			isalnum( byteToInt( ch ) )
  #define isAlpha( ch )			isalpha( byteToInt( ch ) )
  #define isDigit( ch )			isdigit( byteToInt( ch ) )
  #define isPrint( ch )			isprint( byteToInt( ch ) )
  #define isXDigit( ch )		isxdigit( byteToInt( ch ) )
  #define toLower( ch )			tolower( byteToInt( ch ) )
  #define toUpper( ch )			toupper( byteToInt( ch ) )
  #define strCompareZ( str1, str2 )	\
								stricmp( str1, str2 )
  #define strCompare( str1, str2, len )	\
								strnicmp( str1, str2, len )
#endif /* EBCDIC_CHARS */

/* SunOS and older Slowaris have broken sprintf() handling.  In SunOS 4.x
   this was documented as returning a pointer to the output data as per the
   Berkeley original.  Under Slowaris the manpage was changed so that it
   looks like any other sprintf(), but it still returns the pointer to the
   output buffer in some versions so we use a wrapper that checks at
   runtime to see what we've got and adjusts its behaviour accordingly */

#if defined( sun ) && ( OSVERSION <= 5 )
  int fixedSprintf( char *buffer, const int bufSize,
					const char *format, ... );

  #undef sPrintf_s
  #define sPrintf_s				fixedSprintf
#endif /* Old SunOS */

/* Borland C++ before 5.50 doesn't have snprintf() or vsnprintf() */

#if defined( __BORLANDC__ ) && ( __BORLANDC__ < 0x550 )
  #include <stdarg.h>

  int bcSnprintf( char *buffer, const int bufSize,
				  const char *format, ... );
  int bcVsnprintf( char *buffer, const int bufSize,
				   const char *format, va_list argPtr );
#endif /* BC++ before 5.50 */

/****************************************************************************
*																			*
*						TR 24731 Safe stdlib Extensions						*
*																			*
****************************************************************************/

/* ISO/IEC TR 24731 defines alternative stdlib functions designed to perform
   additional parameter checking and avoid some types of common buffer
   overflows.  We use these if possible, if they're not available we map
   them down to the traditional stdlib equivalents, via the preprocessor if
   possible or using wrapper functions if not.  In addition we use the 
   OpenBSD et al strlcpy()/strlcat() functions, whose truncation semantics 
   make them more useful than the TR 24731 equivalents (for example 
   strcpy_s() does nothing on overflow while the equivalent strlcpy() copies
   with truncation).  Microsoft recognise this as well, implementing them in
   TR 24731 by allowing the caller to specify _TRUNCATE semantics */

#ifdef __STDC_LIB_EXT1__
  #if defined( _MSC_VER ) && VC_GE_2005( _MSC_VER )
	/* The VC++ implementation of TR 24731 is based on preliminary versions 
	   of the design for the spec, and in some cases needs re-mapping onto 
	   the final versions.  Instances of this are:
   
		TR 24731: struct tm *gmtime_s( const time_t *timer, struct tm *result );
		VC++: errno_t gmtime_s( struct tm *result, const time_t timer );

	   Because this could potentially result in a circular definition, we 
	   have to kludge in an intermediate layer by renaming the call to 
	   gmTime_s(), which we then remap to the VC++ gmtime_s() */
	#define gmTime_s( timer, result )	\
			( ( gmtime_s( result, timer ) == 0 ) ? result : NULL )

	/* Complicating things further, the Windows DDK doesn't have gmtime_s(),
	   although it does have all of the other TR 24731 functions.  To handle
	   this, we use the same workaround as for the non-TR 24731 libcs */
	#ifdef WIN_DDK
	  #undef gmTime_s
	  #define gmTime_s( timer, result )	gmtime( timer )
	#endif /* WIN_DDK */

	/* MS implements strlcpy/strlcat-equivalents via the TR 24731 
	   functions */
	#define strlcpy_s( s1, s1max, s2 )	strncpy_s( s1, s1max, s2, _TRUNCATE )
	#define strlcat_s( s1, s1max, s2 )	strncat_s( s1, s1max, s2, _TRUNCATE )
  #else
	#define gmTime_s					gmtime_s
  #endif /* VC++ >= 2005 */
#else
  /* String functions.  The OpenBSD strlcpy()/strlcat() functions with their
     truncation semantics are quite useful so we use these as well, 
	 overlaying them with a macro that make them match the TR 24731 look 
	 and feel */
  #define strcpy_s( s1, s1max, s2 )		strcpy( s1, s2 )
  #if defined( __UNIX__ ) && \
	  ( defined( __APPLE__ ) || defined( __FreeBSD__ ) || \
		defined( __NetBSD__ ) || defined( __OpenBSD__ ) || \
		( defined( sun ) && OSVERSION >= 7 ) )
	/* Despite the glibc maintainer's pigheaded opposition to these 
	   functions, some Unix OSes support them via custom libc patches */
	#define strlcpy_s( s1, s1max, s2 )	strlcpy( s1, s2, s1max )	
	#define strlcat_s( s1, s1max, s2 )	strlcat( s1, s2, s1max )
  #else
	int strlcpy_s( char *dest, const int destLen, const char *src );
	int strlcat_s( char *dest, const int destLen, const char *src );
	#define NO_NATIVE_STRLCPY
  #endif /* OpenBSD safe string functions */

  /* Widechar functions */
  int mbstowcs_s( size_t *retval, wchar_t *dst, size_t dstmax, 
				  const char *src, size_t len );
  int wcstombs_s( size_t *retval, char *dst, size_t dstmax, 
				  const wchar_t *src, size_t len );

  /* printf() */
  #if defined( _MSC_VER ) && VC_LT_2005( _MSC_VER )
	#define sprintf_s					_snprintf
	#define vsprintf_s					_vsnprintf
  #elif defined( __BORLANDC__ ) && ( __BORLANDC__ < 0x550 )
	#define sprintf_s					bcSnprintf
	#define vsprintf_s					bcVsnprintf
  #elif defined( __QNX__ ) && ( OSVERSION <= 4 )
	/* snprintf() exists under QNX 4.x but causes a SIGSEGV when called */
	#define sprintf_s					_bprintf
	#define vsnprintf					_vbprintf
  #elif defined( EBCDIC_CHARS )
	/* We provide our own replacements for these functions which handle 
	   output in ASCII (rather than EBCDIC) form */
  #else
    #include <stdio.h>

	#define sprintf_s					snprintf
	#define vsprintf_s					vsnprintf
  #endif /* Compiler-specific safe printf() support */

  /* Misc.functions.  gmtime() is an ugly non-thread-safe function that runs 
     into the same problems as gethostbyname() (see the long comment in 
	 io/tcp.h), to deal with this as best we can we map it to the reentrant 
	 gmtime_r() if it's available.  In addition some OSes use TLS for the
	 result value so it's handled automatically, see the comments in 
	 io/tcp.h for more on this */
  #if defined( USE_THREADS ) && defined( __GLIBC__ ) && ( __GLIBC__ >= 2 ) 
	#define gmTime_s					gmtime_r
  #else
	#define gmTime_s( timer, result )	gmtime( timer )
  #endif /* USE_THREADS and libraries that provide gmtime_r() */
#endif /* TR 24731 safe stdlib extensions */

/****************************************************************************
*																			*
*				Miscellaneous System-specific Support Functions				*
*																			*
****************************************************************************/

/* Perform various operations on pointers */

void *ptr_align( const void *ptr, const int units );
int ptr_diff( const void *ptr1, const void *ptr2 );

/* Check whether a pointer is aligned to a particular value, used by some
   low-level functions that check for potentially unaligned accesses and 
   clean them up if possible.  This is mostly a hygiene check in that if it
   can't be easily implemented we continue anyway but with the possible 
   overhead of an unaligned-access fixup, thus the _OPT qualifier.
   
   The apparently redundant cast to void * before the uintptr_t is necessary 
   because the conversion is only guaranteed for a void *, so if it's some 
   other type of pointer then we have to cast it to a void * first */

#if ( defined( __STDC_VERSION__ ) && ( __STDC_VERSION__ >= 199901L ) ) || \
	( defined( _MSC_VER ) && VC_GE_2005( _MSC_VER ) )
  #define IS_ALIGNED_OPT( pointer, value ) \
		  ( ( ( uintptr_t )( const void * )( pointer ) ) % ( value ) == 0 )
#else
  #define IS_ALIGNED_OPT( pointer, value )	TRUE
#endif /* C99 check */

#endif /* _OSSPEC_DEFINED */
