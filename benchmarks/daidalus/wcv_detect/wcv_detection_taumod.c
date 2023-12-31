// This file is automatically generated by PRECiSA 

#include<stdio.h>
#include<stdlib.h>
#include<math.h>
#include<string.h>
#include<stdbool.h>
#include"precisa_prelude.c"




/*@
axiomatic real_function_tcoa {
logic real tcoa (real sz, real vz) =
((sz * vz) < 0) ? (-((sz / vz))) : (-1);
}
*/


/*@
axiomatic fp_function_tcoa {
logic double tcoa_fp (double sz_double, double vz_double) =
(Dmul(sz_double, vz_double) < (double) (0)) ? (Dneg(Ddiv(sz_double, vz_double))) : ((double) (-1));
}
*/


/*@ axiomatic tcoa_trans {
predicate tcoa_stable_paths (real sz, real vz, double sz_double, double vz_double) =
((! (((sz * vz) < 0)) && (! ((Dmul(sz_double, vz_double) < (double) (0))) && (\true && \true))) || (((sz * vz) < 0) && ((Dmul(sz_double, vz_double) < (double) (0)) && ((vz != 0) && (vz_double != (double) (0))))));
}
*/


/*@
requires (0 <= E_0_double) ;
assigns \nothing;

behavior structure:
ensures (((\is_finite(sz_double) && \is_finite(vz_double)) && \is_finite(E_0_double))
         ==> (equal_fp(\result.value,tcoa_fp(sz_double, vz_double)))) ;

behavior stable_paths:
ensures \forall real sz, real vz; ((\abs(Dmul(sz_double, vz_double) - (sz * vz)) <= E_0_double
                                    ==> (((((\is_finite(sz_double) && \is_finite(vz_double)) && \is_finite(E_0_double)) && \result.isValid)
                                          ==> (tcoa_stable_paths(sz, vz, sz_double, vz_double)))))) ;
*/
struct maybeDouble tcoa_fp (double sz_double, double vz_double, double E_0_double) {
  struct maybeDouble res_double;
  if ((sz_double * vz_double) < - (E_0_double))
  { res_double = someDouble(- ((sz_double / vz_double)));
  } else { if ((sz_double * vz_double) >= E_0_double)
           { res_double = someDouble((double)(-1));
           } else { res_double = noneDouble();
           }
  }
  return res_double;
}


/*@
assigns \nothing;
ensures \forall real sz, real vz; ((((((0 <= sz) && (sz <= 1000)) && ((400 <= vz) && (vz <= 600))) && ((\result.isValid && (\is_finite(sz_double) && \is_finite(vz_double))) && (\abs