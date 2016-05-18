/****************************************************************************
*																			*
*					cryptlib PKC Keygen Header File 						*
*					Copyright Peter Gutmann 1997-2012						*
*																			*
****************************************************************************/

#ifndef _KEYGEN_DEFINED

#define _KEYGEN_DEFINED

/* The number of iterations of Miller-Rabin for an error probbility of
   (1/2)^80, from HAC */

#define getNoPrimeChecks( noBits ) \
	( ( noBits < 150 ) ? 18 : ( noBits < 200 ) ? 15 : \
	  ( noBits < 250 ) ? 12 : ( noBits < 300 ) ? 9 : \
	  ( noBits < 350 ) ? 8 : ( noBits < 400 ) ? 7 : \
	  ( noBits < 500 ) ? 6 : ( noBits < 600 ) ? 5 : \
	  ( noBits < 800 ) ? 4 : ( noBits < 1250 ) ? 3 : 2 )

/* The size of the prime sieve array, 1 memory page (on most CPUs) = 4K 
   candidate values.  When changing this value the LFSR parameters need to 
   be adjusted to match */

#define SIEVE_SIZE				4096

/* Prototypes for functions in ctx_bsieve.c */

STDC_NONNULL_ARG( ( 1, 3 ) ) \
void initSieve( IN_ARRAY( sieveSize ) BOOLEAN *sieveArray, 
				IN_LENGTH_FIXED( SIEVE_SIZE ) const int sieveSize,
				const BIGNUM *candidate );
CHECK_RETVAL_RANGE( 0, SIEVE_SIZE ) \
int nextSievePosition( IN_INT_SHORT int value );
CHECK_RETVAL_RANGE( 0, SIEVE_SIZE ) \
int getSieveEntry( IN_RANGE( 0, SIEVE_SIZE - 1 ) int position );
CHECK_RETVAL_BOOL STDC_NONNULL_ARG( ( 1 ) ) \
BOOLEAN primeSieve( const BIGNUM *candidate );

/* Prototypes for functions in kg_prime.c */

CHECK_RETVAL_RANGE( FALSE, TRUE ) STDC_NONNULL_ARG( ( 1, 2 ) ) \
int primeProbable( INOUT PKC_INFO *pkcInfo, 
				   INOUT BIGNUM *n, 
				   IN_RANGE( 1, 100 ) const int noChecks );
CHECK_RETVAL_RANGE( FALSE, TRUE ) STDC_NONNULL_ARG( ( 1, 2, 3 ) ) \
int primeProbableFermat( INOUT PKC_INFO *pkcInfo, 
						 INOUT BIGNUM *n,
						 INOUT BN_MONT_CTX *montCTX_n );
CHECK_RETVAL STDC_NONNULL_ARG( ( 1, 2 ) ) \
int generatePrime( INOUT PKC_INFO *pkcInfo, 
				   INOUT BIGNUM *candidate, 
				   IN_LENGTH_SHORT_MIN( 120 ) const int noBits, 
				   IN_INT_OPT const long exponent );

#endif /* _KEYGEN_DEFINED */

