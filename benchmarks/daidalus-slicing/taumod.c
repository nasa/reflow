// This file is automatically generated by PRECiSA

#include<stdio.h>
#include<stdlib.h>
#include<math.h>
#include<string.h>
#include<stdbool.h>
#include"precisa_prelude.c"




/*@
axiomatic real_function_taumod {
logic real taumod (real sx, real vx, real sy, real vy, real DTHR) =
(((sx * vx) + (sy * vy)) < 0) ? ((((DTHR * DTHR) - ((sx * sx) + (sy * sy))) / ((sx * vx) + (sy * vy)))) : (-1);
}
*/


/*@
axiomatic fp_function_taumod {
logic double taumod_fp (double sx_double, double vx_double, double sy_double, double vy_double, double DTHR_double) =
(Dadd(Dmul(sx_double, vx_double), Dmul(sy_double, vy_double)) < (double) (0)) ? (Ddiv(Dsub(Dmul(DTHR_double, DTHR_double), Dadd(Dmul(sx_double, sx_double), Dmul(sy_double, sy_double))), Dadd(Dmul(sx_double, vx_double), Dmul(sy_double, vy_double)))) : ((double) (-1));
}
*/


/*@ axiomatic taumod_trans {
predicate taumod_stable_paths (real sx, real vx, real sy, real vy, real DTHR, double sx_double, double vx_double, double sy_double, double vy_double, double DTHR_double) =
((((((sx * vx) + (sy * vy)) != 0) && (((sx * vx) + (sy * vy)) < 0)) && ((Dadd(Dmul(sx_double, vx_double), Dmul(sy_double, vy_double)) != (double) (0)) && (Dadd(Dmul(sx_double, vx_double), Dmul(sy_double, vy_double)) < (double) (0)))) || (! ((((sx * vx) + (sy * vy)) < 0)) && ! ((Dadd(Dmul(sx_double, vx_double), Dmul(sy_double, vy_double)) < (double) (0)))));
}
*/


/*@
requires (0 <= E_0_double) ;
assigns \nothing;

behavior structure:
ensures ((\result.isValid && (\is_finite(\result.value) && (((((\is_finite(sx_double) && \is_finite(vx_double)) && \is_finite(sy_double)) && \is_finite(vy_double)) && \is_finite(DTHR_double)) && \is_finite(E_0_double))))
         ==> ((\result.value == taumod_fp(sx_double, vx_double, sy_double, vy_double, DTHR_double)))) ;

behavior stable_paths:
ensures \forall real sx, real vx, real sy, real vy, real DTHR; ((\abs(Dadd(Dmul(sx_double, vx_double), Dmul(sy_double, vy_double)) - ((sx * vx) + (sy * vy))) <= E_0_double
                                                                 ==> ((((((((\is_finite(sx_double) && \is_finite(vx_double)) && \is_finite(sy_double)) && \is_finite(vy_double)) && \is_finite(DTHR_double)) && \is_finite(E_0_double)) && \result.isValid)
                                                                       ==> (taumod_stable_paths(sx, vx, sy, vy, DTHR, sx_double, vx_double, sy_double, vy_double, DTHR_double)))))) ;
*/
struct maybeDouble taumod_fp (double sx_double, double vx_double, double sy_double, double vy_double, double DTHR_double, double E_0_double) {
  struct maybeDouble res_double;
  if (((sx_double * vx_double) + (sy_double * vy_double)) < - (E_0_double))
  { res_double = someDouble((((DTHR_double * DTHR_double) - ((sx_double * sx_double) + (sy_double * sy_double))) / ((sx_double * vx_double) + (sy_double * vy_double))));
  } else { if (((sx_double * vx_double) + (sy_double * vy_double)) >= E_0_double)
           { res_double = someDouble((double)(-1));
           } else { res_double = noneDouble();
           }
  }
  return res_double;
}


/*@
assigns \nothing;
ensures \forall real sx, real vx, real sy, real vy, real DTHR; (((((((((1 <= sx) && (sx <= 185200)) && ((1 <= sy) && (sy <= 15240))) && ((1 <= vx) && (vx <= 720))) && ((2 <= vy) && (vy <= 720))) && ((670 <= DTHR) && (DTHR <= 670))) && ((\result.isValid && ((((\is_finite(sx_double) && \is_finite(vx_double)) && \is_finite(sy_double)) && \is_finite(vy_double)) && \is_finite(DTHR_double))) && ((((\abs(sx_double - sx) <= ulp_dp(sx)/2 && \abs(vx_double - vx) <= ulp_dp(vx)/2) && \abs(sy_double - sy) <= ulp_dp(sy)/2) && \abs(vy_double - vy) <= ulp_dp(vy)/2) && \abs(DTHR_double - DTHR) <= ulp_dp(DTHR)/2)))
                                                                 ==> ((\abs((\result.value - taumod(sx, vx, sy, vy, DTHR))) <= 0x1.0f5368c5ca9cap-4)))) ;
*/
struct maybeDouble taumod_num (double sx_double, double vx_double, double sy_double, double vy_double, double DTHR_double) {
  return taumod_fp (sx_double, vx_double, sy_double, vy_double, DTHR_double, 0x1.897f000000001p-25);
}

// Decimal: 6.624165465169721e-2 Hex0x1.0f5368c5ca9cap-4
// Decimal: 4.580897439154797e-8 Hex0x1.897f000000001p-25

int main () { return 0; }