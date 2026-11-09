********************************************************************************
* Dirac chain construction with support for transposed contractions and the
* charge conjugation matrix C.
*
* input:  products of single Dirac matrices gamma(x,i,j), where x is a Lorentz
*         index, a vector, g5 or FTxC (the charge conjugation matrix C_ij)
* output: forward Dirac strings gamma(x1,...,xn,i,j); closed strings
*         gamma(x1,...,xn,i,i) are ready to be traced. Open strings are split
*         at orientation changes, so no transposed matrices remain.
*         Closed strings whose value depends on the representation of the
*         Dirac algebra (a leftover C or mixed orientations) are printed as
*         "FTxNonCovariantTrace: ..." and FORM exits; FormTrace reports this
*         as FormTrace::noncovariant.
*
* conventions: C gamma_mu C^-1 = -gamma_mu^T, C gamma5 C^-1 = gamma5^T,
*              C^T = -C, C^-1 = -C (i.e. C C = -1)
*
* internal representation of a string: FTxS(e1,...,en,i,j) with elements
*   FTxF(x) / FTxB(x)   gamma matrix (or slashed vector) x, x^T
*   FTxG5F  / FTxG5B    gamma5, gamma5^T
*   FTxK                C (C^T = -C is normalised immediately)
*
* required declarations:
*   Index FTxC=0; Index FTxsd (with Dirac dimension);
*   CFunction FTxS,FTxSc,FTxF,FTxB,FTxBt,FTxRT,FTxRTL,FTxJ,FTxJL,FTxNonCovTrace;
*   Symbol FTxK,FTxKT,FTxG5F,FTxG5B,FTxG5Bt;
********************************************************************************
#procedure FTxDiracChains

*** fast path: terms without C and without transposed contractions are chained directly
if ( match(gamma(FTxC,spi1?,spi2?)) || match(gamma(?lor1,spi1?,spi2?)*gamma(?lor2,spi3?,spi2?))
     || match(gamma(?lor1,spi2?,spi1?)*gamma(?lor2,spi2?,spi3?)) );
*** wrap single Dirac matrices
  id gamma(g5,spi1?,spi2?) = FTxS(FTxG5F,spi1,spi2);
  id gamma(FTxC,spi1?,spi2?) = FTxS(FTxK,spi1,spi2);
  id gamma(?lor1,spi1?,spi2?) = FTxS(FTxF(?lor1),spi1,spi2);
else;
  repeat id gamma(?lor1,spi1?,spi2?)*gamma(?lor2,spi2?,spi3?) = gamma(?lor1,?lor2,spi1,spi3);
endif;

*** build chains, reading strings in reverse (transposed) where necessary
* X_kj = (X^T)_jk with (x1...xn)^T = xn^T...x1^T
Repeat;
  repeat id FTxS(?lor1,spi1?,spi2?)*FTxS(?lor2,spi2?,spi3?) = FTxS(?lor1,?lor2,spi1,spi3);
* tail-tail: transpose the second string
  id once FTxS(?lor1,spi1?,spi2?)*FTxS(?lor2,spi3?,spi2?) = FTxJ(?lor1,spi1,spi3)*FTxRT(?lor2);
* head-head: transpose the first string
  id once FTxS(?lor1,spi2?,spi1?)*FTxS(?lor2,spi2?,spi3?) = FTxJL(?lor2,spi1,spi3)*FTxRTL(?lor1);
  Transform, FTxRT, FTxRTL, reverse(1,last);
  argument FTxRT, FTxRTL;
    id FTxF(?lor1) = FTxBt(?lor1);
    id FTxB(?lor1) = FTxF(?lor1);
    id FTxBt(?lor1) = FTxB(?lor1);
    id FTxG5F = FTxG5Bt;
    id FTxG5B = FTxG5F;
    id FTxG5Bt = FTxG5B;
    id FTxK = FTxKT;
  endargument;
  id FTxJ(?lor1,spi1?,spi3?)*FTxRT(?lor2) = FTxS(?lor1,?lor2,spi1,spi3);
  id FTxJL(?lor2,spi1?,spi3?)*FTxRTL(?lor1) = FTxS(?lor1,?lor2,spi1,spi3);
* C^T = -C
  repeat id FTxS(?lor1,FTxKT,?lor2) = -FTxS(?lor1,FTxK,?lor2);
EndRepeat;

*** closed strings: FTxSc(e1,...,en,i)
id FTxS(?lor1,spi1?,spi1?) = FTxSc(?lor1,spi1);

*** eliminate pairs of C: C C = -1 and C x = eta_x x^T C, C x^T = eta_x x C
* (eta = -1 for gamma matrices, +1 for gamma5). A C is only moved towards
* another C, so it never leaves a string that contains a single C.
Repeat;
  repeat id FTxS(?lor1,FTxK,FTxK,?lor2) = -FTxS(?lor1,?lor2);
  repeat id FTxSc(?lor1,FTxK,FTxK,?lor2) = -FTxSc(?lor1,?lor2);
  id FTxS(?lor1,FTxK,FTxF(?lor3),?lor2,FTxK,?lor4) = -FTxS(?lor1,FTxB(?lor3),FTxK,?lor2,FTxK,?lor4);
  id FTxS(?lor1,FTxK,FTxB(?lor3),?lor2,FTxK,?lor4) = -FTxS(?lor1,FTxF(?lor3),FTxK,?lor2,FTxK,?lor4);
  id FTxS(?lor1,FTxK,FTxG5F,?lor2,FTxK,?lor4) = FTxS(?lor1,FTxG5B,FTxK,?lor2,FTxK,?lor4);
  id FTxS(?lor1,FTxK,FTxG5B,?lor2,FTxK,?lor4) = FTxS(?lor1,FTxG5F,FTxK,?lor2,FTxK,?lor4);
  id FTxSc(?lor1,FTxK,FTxF(?lor3),?lor2,FTxK,?lor4) = -FTxSc(?lor1,FTxB(?lor3),FTxK,?lor2,FTxK,?lor4);
  id FTxSc(?lor1,FTxK,FTxB(?lor3),?lor2,FTxK,?lor4) = -FTxSc(?lor1,FTxF(?lor3),FTxK,?lor2,FTxK,?lor4);
  id FTxSc(?lor1,FTxK,FTxG5F,?lor2,FTxK,?lor4) = FTxSc(?lor1,FTxG5B,FTxK,?lor2,FTxK,?lor4);
  id FTxSc(?lor1,FTxK,FTxG5B,?lor2,FTxK,?lor4) = FTxSc(?lor1,FTxG5F,FTxK,?lor2,FTxK,?lor4);
EndRepeat;

*** from now on, gamma5 and C are ordinary forward/backward elements
repeat id FTxS(?lor1,FTxG5F,?lor2) = FTxS(?lor1,FTxF(g5),?lor2);
repeat id FTxS(?lor1,FTxG5B,?lor2) = FTxS(?lor1,FTxB(g5),?lor2);
repeat id FTxS(?lor1,FTxK,?lor2) = FTxS(?lor1,FTxF(FTxC),?lor2);
repeat id FTxSc(?lor1,FTxG5F,?lor2) = FTxSc(?lor1,FTxF(g5),?lor2);
repeat id FTxSc(?lor1,FTxG5B,?lor2) = FTxSc(?lor1,FTxB(g5),?lor2);

*** closed strings: a leftover C or mixed orientations are representation dependent
id FTxSc(?lor1,FTxK,?lor2) = FTxNonCovTrace(?lor1,FTxK,?lor2);
id FTxSc(?lor1,FTxF(?lor3),?lor2,FTxB(?lor4),?lor5) = FTxNonCovTrace(?lor1,FTxF(?lor3),?lor2,FTxB(?lor4),?lor5);
id FTxSc(?lor1,FTxB(?lor3),?lor2,FTxF(?lor4),?lor5) = FTxNonCovTrace(?lor1,FTxB(?lor3),?lor2,FTxF(?lor4),?lor5);
id FTxNonCovTrace(?lor1,spi1?) = FTxNonCovTrace(?lor1);
* abort (FormTracer detects the printed message and reports it)
if ( match(FTxNonCovTrace(?lor1)) );
  print "FTxNonCovariantTrace: %t";
  exit "FTxNonCovariantTrace";
endif;
* Tr[x1^T ... xn^T] = Tr[xn ... x1]
id FTxSc(FTxB(?lor1),?lor2) = FTxRTL(FTxB(?lor1),?lor2);
Transform, FTxRTL, reverse(1,last-1);
argument FTxRTL;
  id FTxB(?lor1) = FTxF(?lor1);
endargument;
id FTxRTL(?lor1) = FTxSc(?lor1);
repeat id FTxSc(?lor1,FTxF(?lor3),?lor2) = FTxSc(?lor1,?lor3,?lor2);
id FTxSc(spi1?) = d_(spi1,spi1);
id FTxSc(?lor1,spi1?) = gamma(?lor1,spi1,spi1);

*** open strings: split at orientation changes, (x1^T...xn^T)_ij = (xn...x1)_ji
repeat;
  id once FTxS(?lor1,FTxF(?lor3),FTxB(?lor4),?lor2,spi1?,spi2?) = FTxS(?lor1,FTxF(?lor3),spi1,FTxsd)*FTxS(FTxB(?lor4),?lor2,FTxsd,spi2);
  sum FTxsd;
  id once FTxS(?lor1,FTxB(?lor3),FTxF(?lor4),?lor2,spi1?,spi2?) = FTxS(?lor1,FTxB(?lor3),spi1,FTxsd)*FTxS(FTxF(?lor4),?lor2,FTxsd,spi2);
  sum FTxsd;
endrepeat;
id FTxS(FTxB(?lor1),?lor2,spi1?,spi2?) = FTxRT(FTxB(?lor1),?lor2,spi2,spi1);
Transform, FTxRT, reverse(1,last-2);
id FTxRT(?lor1) = FTxS(?lor1);
repeat id FTxS(?lor1,FTxF(?lor3),?lor2) = FTxS(?lor1,?lor3,?lor2);
repeat id FTxS(?lor1,FTxB(?lor3),?lor2) = FTxS(?lor1,?lor3,?lor2);
id FTxS(spi1?,spi2?) = d_(spi1,spi2);
id FTxS(?lor1,spi1?,spi2?) = gamma(?lor1,spi1,spi2);

#endprocedure
