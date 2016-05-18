/****************************************************************************
*																			*
*						Internal STREAM Header File							*
*					  Copyright Peter Gutmann 1993-2011						*
*																			*
****************************************************************************/

#ifndef _STREAM_INT_DEFINED

#define _STREAM_INT_DEFINED

#if defined( INC_ALL )
  #include "stream.h"
#else
  #include "io/stream.h"
#endif /* Compiler-specific includes */

/****************************************************************************
*																			*
*								Stream Constants							*
*																			*
****************************************************************************/

/* The stream types */

typedef enum {
	STREAM_TYPE_NONE,					/* No stream type */
	STREAM_TYPE_NULL,					/* Null stream (/dev/nul) */
	STREAM_TYPE_MEMORY,					/* Memory stream */
	STREAM_TYPE_FILE,					/* File stream */
	STREAM_TYPE_NETWORK,				/* Network stream */
	STREAM_TYPE_LAST					/* Last possible stream type */
	} STREAM_TYPE;

/* General-purpose stream flags.  These are:

	FLAG_DIRTY: Stream buffer contains data that needs to be committed to
		backing store.

	FLAG_PARTIALREAD: Used for network reads to handle timeouts and for file 
		streams when we don't know the full extent of a file stream.  When 
		this is set and we ask for a read of n bytes and there isn't 
		sufficient data present in the file to satisfy the request the 
		stream code returns 0...n bytes rather than an underflow error.

	FLAG_PARTIALWRITE: Used for network streams when performing bulk data 
		transfers, in this case the write may time out and can be restarted
		later rather than returning a timeout error.

	FLAG_READONLY: Stream is read-only */

#define STREAM_FLAG_NONE		0x0000	/* No stream flag */
#define STREAM_FLAG_READONLY	0x0001	/* Read-only stream */
#define STREAM_FLAG_PARTIALREAD 0x0002	/* Allow read of less than req.amount */
#define STREAM_FLAG_PARTIALWRITE 0x0004	/* Allow write of less than req.amount */
#define STREAM_FLAG_DIRTY		0x0008	/* Stream contains un-committed data */
#define STREAM_FLAG_MASK		0x000F	/* Mask for general-purpose flags */

/* Memory stream flags.  These are:

	MFLAG_PSEUDO/PSEUDO_HTTP/PSEUDO_DIRECT: Used for memory streams 
		emulating some other stream type, writes are discarded and reads 
		come from the stream buffer.  The HTTP flag is an additional 
		modifier to the standard pseudo-stream indicating that it's an
		HTTP-style read, and the RAW flag is an indicator that the HTTP
		stream should read the normally out-of-band header (i.e. the HTTP
		wrapper for an encapsulated data type) as well as the actualy data.  
		These are only available in debug builds since they're used for 
		testing purposes.

	MFLAG_VFILE: The underlying OS doesn't support conventional file I/O (it
		may only support, for example, access to fixed blocks of flash 
		memory) so this is a memory stream emulating a file stream */

#define STREAM_MFLAG_VFILE		0x0020	/* File stream emulated via mem.stream */
#ifndef NDEBUG
  #define STREAM_MFLAG_PSEUDO	0x0040	/* Stream is pseudo-stream */
  #define STREAM_MFLAG_PSEUDO_HTTP 0x0080	/* Stream is HTTP pseudo-stream */
  #define STREAM_MFLAG_PSEUDO_RAW 0x0100	/* Stream reads raw data */
  #define STREAM_MFLAG_MASK		( 0x01E0 | STREAM_FLAG_MASK )	
										/* Mask for memory-only flags */
#else
  #define STREAM_MFLAG_MASK		( 0x0020 | STREAM_FLAG_MASK )	
										/* Mask for memory-only flags */
#endif /* !NDEBUG */

/* File stream flags.  These are:

	FFLAG_BUFFERSET: Used to indicate that the stream has an I/O buffer 
		associated with it.  A stream can be opened without a buffer, but to
		read/write data it needs to have a buffer associated with it.  Since
		this can be of variable size and sometimes isn't required at all, 
		it's created on-demand rather than always being present, and its 
		presence is indicated by this flag.
	
	FFLAG_EOF: The underlying file has reached EOF, no further data can be 
		read once the current buffer is emptied.
	
	FFLAG_MMAPPED: This is a memory-mapped file stream, used in conjunction
		with MFLAG_VFILE virtual file streams.

	FFLAG_POSCHANGED: The position in the underlying file has changed, 
		requiring the file buffer to be refilled from the new position 
		before data can be read from it */

#define STREAM_FFLAG_BUFFERSET	0x0080	/* Stream has associated buffer */
#define STREAM_FFLAG_EOF		0x0100	/* EOF reached on stream */
#define STREAM_FFLAG_POSCHANGED	0x0200	/* File stream position has changed */
#define STREAM_FFLAG_POSCHANGED_NOSKIP 0x0400	/* New stream pos.is in following block */
#define STREAM_FFLAG_MMAPPED	0x0800	/* File stream is memory-mapped */
#define STREAM_FFLAG_MASK		( 0x0F80 | STREAM_FLAG_MASK )	
										/* Mask for file-only flags */

/* Network stream flags.  Since there are quite a number of these and they're
   only required for the network-specific stream functionality, we give them
   their own flags variable instead of using the overall stream flags.  These
   are:

	NFLAG_DGRAM: The stream is run over UDP rather than the default TCP.

	NFLAG_ENCAPS: The protocol is running over a lower encapsulation layer 
		that provides additional packet control information, typically 
		packet size and flow control information.  If this flag is set then
		the lower-level read code overrides some error handling that 
		normally takes place at a higher level.  For example if a read of n 
		bytes is requested and the encapsulation layer reports that only m 
		bytes, m < n is present, this isn't treated as a read/timeout error.

	NFLAG_FIRSTREADOK: The first data read from the stream succeeded.  This
		is used to detect problems due to buggy firewall software, see the
		comments in io/tcp.c for details.

	NFLAG_HTTP10: This is an HTTP 1.0 (rather than 1.1) HTTP stream.

	NFLAG_HTTPPROXY/NFLAG_HTTPTUNNEL: HTTP proxy control flags.  When the 
		proxy flag is set, HTTP requests are sent as 
		"GET http://destination-url/location" (sent to the proxy) rather 
		than "GET location" (sent directly to the target host).  When the 
		tunnel flag is set, the initial network connection-establishment 
		request is sent as an explicit proxy command "CONNECT fqdn:port", 
		after which normal PDUs for the protocol being tunneled are sent.

		Note that the HTTP tunnel flag is currently never set by anything
		due to the removal of the SESSION_USEHTTPTUNNEL flag at a higher
		level, which was only ever set implicitly by being set in the 
		SSL/TLS altProtocolInfo, which in turn was never selected outside
		a USE_CMP_TRANSPORT block.  The location at which it would be
		selected (except for the presence of a USE_CMP_TRANSPORT ifdef) is 
		at line 195 of session/sess_attr.c in versions up to 3.4.1.

	NFLAG_HTTPGET/NFLAG_HTTPPOST: HTTP allowed-actions flags.

	NFLAG_HTTPPOST_AS_GET: Modify the POST to encode it as a GET (ugh), for 
		b0rken servers that don't do POST.

	NFLAG_ISSERVER: The stream is a server stream (default is client).

	NFLAG_LASTMSGR/NFLAG_LASTMSGR: This is the last message in the exchange.
		For a last-message read it means that the other side has indicated
		(for example through an HTTP "Connection: close") that this is the 
		case.  For a last-message write it means that we should indicate to
		the other side (for example through an HTTP "Connection: close") 
		that this is the case.

	NFLAG_USERSOCKET: The network socket was supplied by the user rather 
		than being created by cryptlib, so some actions such as socket
		shutdown should be skipped */

#define STREAM_NFLAG_ISSERVER	0x0001	/* Stream is server rather than client */
#define STREAM_NFLAG_USERSOCKET	0x0002	/* Network socket was supplied by user */
#define STREAM_NFLAG_DGRAM		0x0004	/* Stream is UDP rather than TCP */
#define STREAM_NFLAG_HTTP10		0x0008	/* HTTP 1.0 stream */
#define STREAM_NFLAG_HTTPPROXY	0x0010	/* Use HTTP proxy format for requests */
#define STREAM_NFLAG_HTTPTUNNEL	0x0020	/* Use HTTP proxy tunnel for connect */
#define STREAM_NFLAG_HTTPGET	0x0040	/* Allow HTTP GET */
#define STREAM_NFLAG_HTTPPOST	0x0080	/* Allow HTTP POST */
#define STREAM_NFLAG_HTTPPOST_AS_GET 0x0100	/* Implement POST as GET */
#define STREAM_NFLAG_LASTMSGR	0x0200	/* Last message in exchange */
#define STREAM_NFLAG_LASTMSGW	0x0400	/* Last message in exchange */
#define STREAM_NFLAG_ENCAPS		0x0800	/* Network transport is encapsulated */
#define STREAM_NFLAG_FIRSTREADOK 0x1000	/* First data read succeeded */
#define STREAM_NFLAG_HTTPREQMASK ( STREAM_NFLAG_HTTPGET | STREAM_NFLAG_HTTPPOST | \
								   STREAM_NFLAG_HTTPPOST_AS_GET )
										/* Mask for permitted HTTP req.types */

/* Network transport-specific flags.  These are:

	FLAG_FLUSH: Used in writes to buffered streams to force a flush of data in 
		the stream buffers.
	
	FLAG_BLOCKING/FLAG_NONBLOCKING: Used to override the stream default 
		behaviour on reads and writes and force blocking/nonblocking I/O */

#define TRANSPORT_FLAG_NONE		0x00	/* No transport flag */
#define TRANSPORT_FLAG_FLUSH	0x01	/* Flush data on write */
#define TRANSPORT_FLAG_NONBLOCKING 0x02	/* Explicitly perform nonblocking read */
#define TRANSPORT_FLAG_BLOCKING	0x04	/* Explicitly perform blocking read */
#define TRANSPORT_FLAG_MAX		0x07	/* Maximum possible flag value */

/* The size of the memory buffer used for virtual file streams, which are 
   used in CONFIG_NO_STDIO environments to store data before it's committed
   to backing storage */

#if defined( __MVS__ ) || defined( __VMCMS__ ) || \
	defined( __IBM4758__ ) || defined( __TESTIO__ )
  #define VIRTUAL_FILE_STREAM
#endif /* Nonstandard I/O environments */

#define STREAM_VFILE_BUFSIZE	16384

/****************************************************************************
*																			*
*								Stream Structures							*
*																			*
****************************************************************************/

#ifdef USE_TCP

/* The network-stream specific information stored as part of the STREAM
   data type */

struct NS;

typedef CHECK_RETVAL_BOOL STDC_NONNULL_ARG( ( 1 ) ) \
		BOOLEAN ( *STM_SANITYCHECK_FUNCTION )( IN const struct ST *stream );
typedef CHECK_RETVAL STDC_NONNULL_ARG( ( 1, 2, 4 ) ) \
		int ( *STM_READ_FUNCTION )( INOUT struct ST *stream, 
									OUT_BUFFER( maxLength, *length ) \
										void *buffer, 
									IN_DATALENGTH const int maxLength, 
									OUT_DATALENGTH_Z int *length );
typedef CHECK_RETVAL STDC_NONNULL_ARG( ( 1, 2, 4 ) ) \
		int ( *STM_WRITE_FUNCTION )( INOUT struct ST *stream, 
									 IN_BUFFER( maxLength ) \
										const void *buffer, 
									 IN_DATALENGTH const int maxLength,
									 OUT_DATALENGTH_Z int *length );
typedef CHECK_RETVAL STDC_NONNULL_ARG( ( 1, 2 ) ) \
		int ( *STM_TRANSPORTCONNECT_FUNCTION )( INOUT struct NS *netStream, 
												IN_BUFFER_OPT( hostNameLen ) \
													const char *hostName,
												IN_LENGTH_DNS_Z \
													const int hostNameLen, 
												IN_PORT const int port );
typedef STDC_NONNULL_ARG( ( 1 ) ) \
		void ( *STM_TRANSPORTDISCONNECT_FUNCTION )( INOUT struct NS *netStream, 
													const BOOLEAN fullDisconnect );
typedef CHECK_RETVAL STDC_NONNULL_ARG( ( 1, 2, 4 ) ) \
		int ( *STM_TRANSPORTREAD_FUNCTION )( INOUT struct ST *stream, 
											 OUT_BUFFER( maxLength, *length ) \
												BYTE *buffer, 
											 IN_DATALENGTH const int maxLength, 
											 OUT_DATALENGTH_Z int *length, 
											 IN_FLAGS_Z( TRANSPORT ) \
												const int flags );
typedef CHECK_RETVAL STDC_NONNULL_ARG( ( 1, 2, 4 ) ) \
		int ( *STM_TRANSPORTWRITE_FUNCTION )( INOUT struct ST *stream, 
											  IN_BUFFER( maxLength ) \
												const BYTE *buffer,
											  IN_DATALENGTH const int maxLength, 
											  OUT_DATALENGTH_Z int *length, 
											  IN_FLAGS_Z( TRANSPORT ) \
												const int flags );
typedef CHECK_RETVAL_BOOL \
		BOOLEAN ( *STM_TRANSPORTOK_FUNCTION )( void );
typedef CHECK_RETVAL STDC_NONNULL_ARG( ( 1 ) ) \
		int ( *STM_TRANSPORTCHECK_FUNCTION )( INOUT struct NS *netStream );
typedef CHECK_RETVAL STDC_NONNULL_ARG( ( 1, 2, 4 ) ) \
		int ( *STM_BUFFEREDTRANSPORTREAD_FUNCTION )( INOUT struct ST *stream, 
													 OUT_BUFFER( maxLength, *length ) \
														BYTE *buffer, 
													 IN_DATALENGTH \
														const int maxLength, 
													 OUT_DATALENGTH_Z int *length, 
													 IN_FLAGS_Z( TRANSPORT ) \
														const int flags );
typedef CHECK_RETVAL STDC_NONNULL_ARG( ( 1, 2, 4 ) ) \
		int ( *STM_BUFFEREDTRANSPORTWRITE_FUNCTION )( INOUT struct ST *stream, 
													  IN_BUFFER( maxLength ) \
														const BYTE *buffer,
													  IN_DATALENGTH \
														const int maxLength, 
													  OUT_DATALENGTH_Z int *length, 
													  IN_FLAGS_Z( TRANSPORT ) \
														const int flags );

typedef struct NS {
	/* General information for the network stream.  For a server the
	   listenSocket is the (possibly shared) common socket that the server 
	   is listening on, the netSocket is the ephemeral socket used for
	   communications */
	STREAM_PROTOCOL_TYPE protocol;/* Network protocol type */
	int nFlags;					/* Network-specific flags */
	int netSocket, listenSocket;/* Network socket */
	CRYPT_SESSION iTransportSession;/* cryptlib session as transport layer */

	/* Network timeout information.  The timeout value depends on whether 
	   the stream is in the connect/handshake phase or the data transfer 
	   phase.  The handshake phase is logically treated as part of the 
	   connect phase even though from the stream point of view it's part of 
	   the data transfer phase.  Initially the stream timeout is set to the 
	   connect timeout and the saved timeout is set to the data transfer 
	   timeout.  Once the connect/handshake has completed, the stream 
	   timeout is set to the saved data transfer timeout and the saved 
	   timeout is cleared */
	int timeout, savedTimeout;	/* Network comms timeout */

	/* Network streams require separate read/write buffers for packet
	   assembly/disassembly so we provide a write buffer alongside the 
	   generic stream read buffer */
	BUFFER( writeBufSize, writeBufEnd ) \
	BYTE *writeBuffer;			/* Write buffer */
	int writeBufSize;			/* Total size of buffer */
	int writeBufEnd;			/* Last buffer position with valid data */

	/* General network-related information.  The server FQDN is held in 
	   dynamically-allocated storage, the optional path for HTTP is a pointer 
	   into the host string at the appropriate location */
	BUFFER_FIXED( hostLen ) \
	char *host;
	int hostLen;
	BUFFER_OPT_FIXED( pathLen ) \
	char *path;
	int pathLen;
	int port;					/* Host name, path on host, and port */
	BUFFER( CRYPT_MAX_TEXTSIZE / 2, clientAddressLen ) \
	char clientAddress[ ( CRYPT_MAX_TEXTSIZE / 2 ) + 4 ];
	int clientAddressLen;		/* Client IP address (dotted-decimal) */
	int clientPort;				/* Client port */

	/* Sometimes we can fingerprint the application running on the peer 
	   system, which is useful for working around buggy implementations.  
	   The following value stores the peer application type, if known */
	STREAM_PEER_TYPE systemType;

	/* If a network error condition is fatal we set the persistentStatus 
	   value.  This is checked by the higher-level stream code and copied 
	   to to stream persistent status if required */
	int persistentStatus;

	/* Last-error information returned from lower-level code */
	ERROR_INFO errorInfo;

	/* Network stream access functions.  The general read and write 
	   functions are for the higher-level network access routines such as 
	   HTTP and CMP I/O, the transport I/O functions are for transport-level 
	   I/O that sits below the general I/O.  Finally, there's an 
	   intermediate function that adds speculative read-ahead buffering to 
	   the transport-level read to improve performance for higher-level 
	   protocols like HTTP that have to read a byte at a time in some 
	   places */
	FNPTR_DECLARE( STM_SANITYCHECK_FUNCTION, sanityCheckFunction );
	FNPTR_DECLARE( STM_READ_FUNCTION, readFunction );
	FNPTR_DECLARE( STM_WRITE_FUNCTION, writeFunction );
	FNPTR_DECLARE( STM_TRANSPORTCONNECT_FUNCTION, transportConnectFunction );
	FNPTR_DECLARE( STM_TRANSPORTDISCONNECT_FUNCTION, transportDisconnectFunction );
	FNPTR_DECLARE( STM_TRANSPORTREAD_FUNCTION, transportReadFunction );
	FNPTR_DECLARE( STM_TRANSPORTWRITE_FUNCTION, transportWriteFunction );
	FNPTR_DECLARE( STM_TRANSPORTOK_FUNCTION, transportOKFunction );
	FNPTR_DECLARE( STM_TRANSPORTCHECK_FUNCTION, transportCheckFunction );
	FNPTR_DECLARE( STM_BUFFEREDTRANSPORTREAD_FUNCTION, bufferedTransportReadFunction );
	FNPTR_DECLARE( STM_BUFFEREDTRANSPORTWRITE_FUNCTION, bufferedTransportWriteFunction );

	/* Variable-length storage for the stream buffers */
	DECLARE_VARSTRUCT_VARS;
	} NET_STREAM_INFO;
#else

typedef void *NET_STREAM_INFO;	/* Dummy for function prototypes */

#endif /* USE_TCP */

/****************************************************************************
*																			*
*							Stream Function Prototypes						*
*																			*
****************************************************************************/

/* Stream query functions to determine whether a stream is a memory-mapped 
   file stream, a virtual file stream, or a pseudo-stream.  The memory-
   mapped stream check is used when we can eliminate extra buffer allocation 
   if all data is available in memory.  The virtual file stream check is 
   used where the low-level access routines have converted a file on a 
   CONFIG_NO_STDIO system to a memory stream that acts like a file stream.
   The pseudo-stream is used for testing purposes to emulate a standard
   stream like a network stream */

#define sIsMemMappedStream( stream ) \
		( ( ( stream )->type == STREAM_TYPE_FILE ) && \
		  ( ( stream )->flags & STREAM_FFLAG_MMAPPED ) )
#ifdef VIRTUAL_FILE_STREAM 
  #define sIsVirtualFileStream( stream ) \
		  ( ( ( stream )->type == STREAM_TYPE_MEMORY ) && \
			( ( stream )->flags & STREAM_MFLAG_VFILE ) )
#else
  #define sIsVirtualFileStream( stream )	FALSE
#endif /* VIRTUAL_FILE_STREAM */
#ifndef NDEBUG
  #define sIsPseudoStream( stream ) \
		  ( ( ( stream )->type == STREAM_TYPE_MEMORY ) && \
			( ( stream )->flags & STREAM_MFLAG_PSEUDO ) )
  #define sIsPseudoHTTPStream( stream ) \
		  ( ( ( stream )->type == STREAM_TYPE_MEMORY ) && \
			( ( stream )->flags & STREAM_MFLAG_PSEUDO_HTTP ) )
  #define sIsPseudoHTTPRawStream( stream ) \
		  ( ( ( stream )->type == STREAM_TYPE_MEMORY ) && \
			( ( ( stream )->flags & \
				( STREAM_MFLAG_PSEUDO_HTTP | STREAM_MFLAG_PSEUDO_RAW ) ) == \
				( STREAM_MFLAG_PSEUDO_HTTP | STREAM_MFLAG_PSEUDO_RAW ) ) )
#endif /* !NDEBUG */

/* Prototypes for functions in file.c */

#ifdef USE_FILES
CHECK_RETVAL STDC_NONNULL_ARG( ( 1, 2, 4 ) ) \
int fileRead( INOUT STREAM *stream, 
			  OUT_BUFFER( length, *bytesRead ) void *buffer, 
			  IN_DATALENGTH const int length, 
			  OUT_DATALENGTH_Z int *bytesRead );
CHECK_RETVAL STDC_NONNULL_ARG( ( 1, 2 ) ) \
int fileWrite( INOUT STREAM *stream, 
			   IN_BUFFER( length ) const void *buffer, 
			   IN_DATALENGTH const int length );
CHECK_RETVAL STDC_NONNULL_ARG( ( 1 ) ) \
int fileFlush( INOUT STREAM *stream );
CHECK_RETVAL STDC_NONNULL_ARG( ( 1 ) ) \
int fileSeek( INOUT STREAM *stream,
			  IN_DATALENGTH_Z const long position );
#endif /* USE_FILES */

/* Network URL processing functions in net_url.c */

CHECK_RETVAL STDC_NONNULL_ARG( ( 1, 2 ) ) \
int parseURL( OUT URL_INFO *urlInfo, 
			  IN_BUFFER( urlLen ) const BYTE *url, 
			  IN_LENGTH_SHORT const int urlLen,
			  IN_PORT_OPT const int defaultPort, 
			  IN_ENUM_OPT( URL_TYPE ) const URL_TYPE urlTypeHint,
			  const BOOLEAN preParseOnly );

/* Network proxy functions in net_proxy.c */

CHECK_RETVAL STDC_NONNULL_ARG( ( 1 ) ) \
int connectViaSocksProxy( INOUT STREAM *stream );
CHECK_RETVAL STDC_NONNULL_ARG( ( 1, 2 ) ) \
int connectViaHttpProxy( INOUT STREAM *stream, 
						 INOUT ERROR_INFO *errorInfo );
#if defined( __WIN32__ )
CHECK_RETVAL STDC_NONNULL_ARG( ( 1, 3, 4 ) ) \
  int findProxyUrl( OUT_BUFFER( proxyMaxLen, *proxyLen ) char *proxy, 
					IN_LENGTH_DNS const int proxyMaxLen, 
					OUT_LENGTH_BOUNDED_Z( proxyMaxLen ) int *proxyLen,
					IN_BUFFER( urlLen ) const char *url, 
					IN_LENGTH_DNS const int urlLen );
#else
  #define findProxyUrl( proxy, proxyMaxLen, proxyLen, url, urlLen )	CRYPT_ERROR_NOTFOUND
#endif /* Win32 */

/* Network access mapping functions */

STDC_NONNULL_ARG( ( 1 ) ) \
void setAccessMethodTCP( INOUT NET_STREAM_INFO *netStream );
STDC_NONNULL_ARG( ( 1 ) ) \
void setStreamLayerHTTP( INOUT NET_STREAM_INFO *netStream );
STDC_NONNULL_ARG( ( 1 ) ) \
void setStreamLayerCMP( INOUT NET_STREAM_INFO *netStream );
STDC_NONNULL_ARG( ( 1 ) ) \
void setStreamLayerDirect( INOUT NET_STREAM_INFO *netStream );
STDC_NONNULL_ARG( ( 1 ) ) \
void setStreamLayerBuffering( INOUT NET_STREAM_INFO *netStream,
							  const BOOLEAN useTransportBuffering );
#if 0	/* See comment in net_trans.c */
STDC_NONNULL_ARG( ( 1 ) ) \
void setAccessMethodTransportSession( INOUT NET_STREAM_INFO *netStream );
#else
#define setAccessMethodTransportSession( netStream )
#endif /* 0 */

#endif /* _STREAM_INT_DEFINED */
