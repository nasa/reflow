// This file is automatically generated by PRECiSA 

#include<stdio.h>
#include<stdlib.h>
#include<math.h>
#include<string.h>
#include<stdbool.h>
#include"precisa_prelude.c"




/*@
axiomatic real_pred_horizontal_WCV_taumod_interval {
logic boolean horizontal_WCV_taumod_interval (real T, real sx, real sy, real vx, real vy, real TAUMOD, real DTHR) =
((DTHR * DTHR) <= 0);
}
*/


/*@
axiomatic fp_pred_horizontal_WCV_taumod_interval {
logic boolean horizontal_WCV_taumod_interval_fp (double T_double, double sx_double, double sy_double, double vx_double, double vy_double, double TAUMOD_double, double DTHR_double) =
(Dmul(DTHR_double, DTHR_double) <= (double) (0));
}
*/


/*@
requires (0 <= E_0_double) ;
assigns \nothing;

behavior structure:
ensures \forall real T, real sx, real sy, real vx, real vy, real TAUMOD, real DTHR; (((((((((\is_finite(T_double) && \is_finite(sx_double)) && \is_finite(sy_double)) && \is_finite(vx_double)) && \is_finite(vy_double)) && \is_finite(TAUMOD_double)) && \is_finite(DTHR_double)) && \is_finite(E_0_double))
                                                                                      ==> ((\result
                                                                                            ==> ((horizontal_WCV_taumod_interval(T, sx, sy, vx, vy, TAUMOD, DTHR) && horizontal_WCV_taumod_interval_fp(T_double, sx_double, sy_double, vx_double, vy_double, TAUMOD_double, DTHR_double))))))) ;
*/
bool horizontal_WCV_taumod_interval_tauplus_fp (double T_double, double sx_double, double sy_double, double vx_double, double vy_double, double TAUMOD_double, double DTHR_double, double E_0_double) {
  bool res;
  res = (DTHR_double * DTHR_double) <= - (E_0_double);
  return res;
}


/*@
assigns \nothing;
ensures \forall real T, real sx, real sy, real vx, real vy, real TAUMOD, real DTHR; (((((((((((1 <= T) && (T <= 10)) && ((1 <= sx) && (sx <= 2))) && ((1 <= vx) && (vx <= 2))) && ((1 <= sy) && (sy <= 2))) && ((1 <= vy) && (vy <= 2))) && ((1 <= TAUMOD) && (TAUMOD <= 2))) && ((1 <= DTHR) && (DTHR <= 3))) && (((((((\is_finite(T_double) && \is_finite(sx_double)) && \is_finite(sy_double)) && \is_finite(vx_double)) && \is_finite(vy_double)) && \is_finite(TAUMOD_double)) && \is_finite(DTHR_double)) && ((((((\abs(T_double - T) <= ulp_dp(T)/2 && \abs(sx_double - sx) <= ulp_dp(sx)/2) && \abs(sy_double - sy) <= ulp_dp(sy)/2) && \abs(vx_double - vx) <= ulp_dp(vx)/2) && \abs(vy_double - vy) <= ulp_dp(vy)/2) && \abs(TAUMOD_double - TAUMOD) <= ulp_dp(TAUMOD)/2) && \abs(DTHR_double - DTHR) <= ulp_dp(DTHR)/2)))
                                                                                      ==> ((\result
                                                                                            ==> (horizontal_WCV_taumod_interval(T, sx, sy, vx, vy, TAUMOD, DTHR)))))) ;
*/
bool horizontal_WCV_taumod_interval_tauplus_num (double T_double, double sx_double, double sy_double, double vx_double, double vy_double, double TAUMOD_double, double DTHR_double) {
  return horizontal_WCV_taumod_interval_tauplus_fp (T_double, sx_double, sy_double, vx_double, vy_double, TAUMOD_double, DTHR_double, 0x1.4000000000001p-49);
}




/*@
requires (0 <= E_0_double) ;
assigns \nothing;

behavior structure:
ensures \forall real T, real sx, real sy, real vx, real vy, real TAUMOD, real DTHR; (((((((((\is_finite(T_double) && \is_finite(sx_double)) && \is_finite(sy_double)) && \is_finite(vx_double)) && \is_finite(vy_double)) && \is_finite(TAUMOD_double)) && \is_finite(DTHR_double)) && \is_finite(E_0_double))
                                                                                      ==> ((\result
                                                                                            ==> ((! (horizontal_WCV_taumod_interval(T, sx, sy, vx, vy, TAUMOD, DTHR)) && ! (horizontal_WCV_taumod_interval_fp(T_double, sx_double, sy_double, vx_double, vy_double, TAUMOD_double, DTHR_double)))))))) ;
*/
bool horizontal_WCV_taumod_interval_tauminus_fp (double T_double, double sx_double, double sy_double, double vx_double, double vy_double, double TAUMOD_double, double DTHR_double, double E_0_double) {
  bool res;
  res = (DTHR_double * DTHR_double) > E_0_double;
  return res;
}


/*@
assigns \nothing;
ensures \forall real T, real sx, real sy, real vx, real vy, real TAUMOD, real DTHR; (((((((((((1 <= T) && (T <= 10)) && ((1 <= sx) && (sx <= 2))) && ((1 <= vx) && (vx <= 2))) && ((1 <= sy) && (sy <= 2))) && ((1 <= vy) && (vy <= 2))) && ((1 <= TAUMOD) && (TAUMOD <= 2))) && ((1 <= DTHR) && (DTHR <= 3))) && (((((((\is_finite(T_double) && \is_finite(sx_double)) && \is_finite(sy_double)) && \is_finite(vx_double)) && \is_finite(vy_double)) && \is_finite(TAUMOD_double)) && \is_finite(DTHR_double)) && ((((((\abs(T_double - T) <= ulp_dp(T)/2 && \abs(sx_double - sx) <= ulp_dp(sx)/2) && \abs(sy_double - sy) <= ulp_dp(sy)/2) && \abs(vx_double - vx) <= ulp_dp(vx)/2) && \abs(vy_double - vy) <= ulp_dp(vy)/2) && \abs(TAUMOD_double - TAUMOD) <= ulp_dp(TAUMOD)/2) && \abs(DTHR_double - DTHR) <= ulp_dp(DTHR)/2)))
                                                                                      ==> ((\result
                                                                                            ==> (! (horizontal_WCV_taumod_interval(T, sx, sy, vx, vy, TAUMOD, DTHR))))))) ;
*/
bool horizontal_WCV_taumod_interval_tauminus_num (double T_double, double sx_double, double sy_double, double vx_double, double vy_double, double TAUMOD_double, double DTHR_double) {
  return horizontal_WCV_taumod_interval_tauminus_fp (T_double, sx_double, sy_double, vx_double, vy_double, TAUMOD_double, DTHR_double, 0x1.4000000000001p-49);
}


/*@
axiomatic real_function_vertical_WCV_exit_minus_entry {
logic real vertical_WCV_exit_minus_entry (real B, real T, real sz, real vz, real TCOA, real ZTHR) =
TCOA;
}
*/


/*@
axiomatic fp_function_vertical_WCV_exit_minus_entry {
logic double vertical_WCV_exit_minus_entry_fp (double B_double, double T_double, double sz_double, double vz_double, double TCOA_double, double ZTHR_double) =
TCOA_double;
}
*/


/*@
assigns \nothing;

behavior structure:
ensures ((\is_finite(\result) && (((((\is_finite(B_double) && \is_finite(T_double)) && \is_finite(sz_double)) && \is_finite(vz_double)) && \is_finite(TCOA_double)) && \is_finite(ZTHR_double)))
         ==> ((\result == vertical_WCV_exit_minus_entry_fp(B_double, T_double, sz_double, vz_double, TCOA_double, ZTHR_double)))) ;
*/
double vertical_WCV_exit_minus_entry_fp (double B_double, double T_double, double sz_double, double vz_double, double TCOA_double, double ZTHR_double) {
  double res_double;
  res_double = TCOA_double;
  return res_double;
}


/*@
assigns \nothing;
ensures \forall real B, real T, real sz, real vz, real TCOA, real ZTHR; ((((((((((1 <= B) && (B <= 10)) && ((1 <= T) && (T <= 10))) && ((1 <= sz) && (sz <= 2))) && ((1 <= vz) && (vz <= 2))) && ((2 <= TCOA) && (TCOA <= 3))) && ((2 <= ZTHR) && (ZTHR <= 3))) && ((((((\is_finite(B_double) && \is_finite(T_double)) && \is_finite(sz_double)) && \is_finite(vz_double)) && \is_finite(TCOA_double)) && \is_finite(ZTHR_double)) && (((((\abs(B_double - B) <= ulp_dp(B)/2 && \abs(T_double - T) <= ulp_dp(T)/2) && \abs(sz_double - sz) <= ulp_dp(sz)/2) && \abs(vz_double - vz) <= ulp_dp(vz)/2) && \abs(TCOA_double - TCOA) <= ulp_dp(TCOA)/2) && \abs(ZTHR_double - ZTHR) <= ulp_dp(ZTHR)/2)))
                                                                          ==> ((\abs((\result - vertical_WCV_exit_minus_entry(B, T, sz, vz, TCOA, ZTHR))) <= 0x1p-52)))) ;
*/
double vertical_WCV_exit_minus_entry_num (double B_double, double T_double, double sz_double, double vz_double, double TCOA_double, double ZTHR_double) {
  return vertical_WCV_exit_minus_entry_fp (B_double, T_double, sz_double, vz_double, TCOA_double, ZTHR_double);
}


/*@
axiomatic real_pred_WCV_interval {
logic boolean WCV_interval (real B, real T, real sx, real sy, real sz, real vx, real vy, real vz, real TAUMOD, real TCOA, real DTHR, real TTHR, real ZTHR) =
((vertical_WCV_exit_minus_entry(B, T, sz, vz, TCOA, ZTHR) < 0))
? \false :
((vertical_WCV_exit_minus_entry(B, T, sz, vz, TCOA, ZTHR) > 0))
? horizontal_WCV_taumod_interval(vertical_WCV_exit_minus_entry(B, T, sz, vz, TCOA, ZTHR), B, B, vx, vy, TAUMOD, DTHR) :
\false;
}
*/


/*@
axiomatic fp_pred_WCV_interval {
logic boolean WCV_interval_fp (double B_double, double T_double, double sx_double, double sy_double, double sz_double, double vx_double, double vy_double, double vz_double, double TAUMOD_double, double TCOA_double, double DTHR_double, double TTHR_double, double ZTHR_double) =
((vertical_WCV_exit_minus_entry_fp(B_double, T_double, sz_double, vz_double, TCOA_double, ZTHR_double) < (double) (0)))
? \false :
((vertical_WCV_exit_minus_entry_fp(B_double, T_double, sz_double, vz_double, TCOA_double, ZTHR_double) > (double) (0)))
? horizontal_WCV_taumod_interval_fp(vertical_WCV_exit_minus_entry_fp(B_double, T_double, sz_double, vz_double, TCOA_double, ZTHR_double), B_double, B_double, vx_double, vy_double, TAUMOD_double, DTHR_double) :
\false;
}
*/


/*@ axiomatic WCV_interval_tauplus_trans {
predicate WCV_interval_tauplus_stable_paths (real B, real T, real sx, real sy, real sz, real vx, real vy, real vz, real TAUMOD, real TCOA, real DTHR, real TTHR, real ZTHR, double B_double, double T_double, double sx_double, double sy_double, double sz_double, double vx_double, double vy_double, double vz_double, double TAUMOD_double, double TCOA_double, double DTHR_double, double TTHR_double, double ZTHR_double) =
((((! ((vertical_WCV_exit_minus_entry(B, T, sz, vz, TCOA, ZTHR) > 0)) && ! ((vertical_WCV_exit_minus_entry(B, T, sz, vz, TCOA, ZTHR) < 0))) && ((! ((vertical_WCV_exit_minus_entry_fp(B_double, T_double, sz_double, vz_double, TCOA_double, ZTHR_double) > (double) (0))) && ! ((vertical_WCV_exit_minus_entry_fp(B_double, T_double, sz_double, vz_double, TCOA_double, ZTHR_double) < (double) (0)))) && (\true && \true))) || (((vertical_WCV_exit_minus_entry(B, T, sz, vz, TCOA, ZTHR) > 0) && ! ((vertical_WCV_exit_minus_entry(B, T, sz, vz, TCOA, ZTHR) < 0))) && (((vertical_WCV_exit_minus_entry_fp(B_double, T_double, sz_double, vz_double, TCOA_double, ZTHR_double) > (double) (0)) && ! ((vertical_WCV_exit_minus_entry_fp(B_double, T_double, sz_double, vz_double, TCOA_double, ZTHR_double) < (double) (0)))) && (\true && \true)))) || ((vertical_WCV_exit_minus_entry(B, T, sz, vz, TCOA, ZTHR) < 0) && ((vertical_WCV_exit_minus_entry_fp(B_double, T_double, sz_double, vz_double, TCOA_double, ZTHR_double) < (double) (0)) && (\true && \true))));
}
*/


/*@
requires ((0 <= E_0_double) && (0 <= E_1_double)) ;
assigns \nothing;

behavior structure:
ensures \forall real B, real T, real sx, real sy, real sz, real vx, real vy, real vz, real TAUMOD, real TCOA, real DTHR, real TTHR, real ZTHR; (((\result.isValid && ((((((((((((((\is_finite(B_double) && \is_finite(T_double)) && \is_finite(sx_double)) && \is_finite(sy_double)) && \is_finite(sz_double)) && \is_finite(vx_double)) && \is_finite(vy_double)) && \is_finite(vz_double)) && \is_finite(TAUMOD_double)) && \is_finite(TCOA_double)) && \is_finite(DTHR_double)) && \is_finite(TTHR_double)) && \is_finite(ZTHR_double)) && \is_finite(E_0_double)) && \is_finite(E_1_double)))
                                                                                                                                                 ==> ((\result.value
                                                                                                                                                       ==> ((WCV_interval(B, T, sx, sy, sz, vx, vy, vz, TAUMOD, TCOA, DTHR, TTHR, ZTHR) && WCV_interval_fp(B_double, T_double, sx_double, sy_double, sz_double, vx_double, vy_double, vz_double, TAUMOD_double, TCOA_double, DTHR_double, TTHR_double, ZTHR_double))))))) ;

behavior stable_paths:
ensures \forall real B, real T, real sx, real sy, real sz, real vx, real vy, real vz, real TAUMOD, real TCOA, real DTHR, real TTHR, real ZTHR; (((\abs(vertical_WCV_exit_minus_entry_fp(B_double, T_double, sz_double, vz_double, TCOA_double, ZTHR_double) - vertical_WCV_exit_minus_entry(B, T, sz, vz, TCOA, ZTHR)) <= E_0_double && \abs(Dmul(DTHR_double, DTHR_double) - (DTHR * DTHR)) <= E_1_double)
                                                                                                                                                 ==> (((((((((((((((((\is_finite(B_double) && \is_finite(T_double)) && \is_finite(sx_double)) && \is_finite(sy_double)) && \is_finite(sz_double)) && \is_finite(vx_double)) && \is_finite(vy_double)) && \is_finite(vz_double)) && \is_finite(TAUMOD_double)) && \is_finite(TCOA_double)) && \is_finite(DTHR_double)) && \is_finite(TTHR_double)) && \is_finite(ZTHR_double)) && \is_finite(E_0_double)) && \is_finite(E_1_double)) && \result.isValid)
                                                                                                                                                       ==> (WCV_interval_tauplus_stable_paths(B, T, sx, sy, sz, vx, vy, vz, TAUMOD, TCOA, DTHR, TTHR, ZTHR, B_double, T_double, sx_double, sy_double, sz_double, vx_double, vy_double, vz_double, TAUMOD_double, TCOA_double, DTHR_double, TTHR_double, ZTHR_double)))))) ;
*/
struct maybeBool WCV_interval_tauplus_fp (double B_double, double T_double, double sx_double, double sy_double, double sz_double, double vx_double, double vy_double, double vz_double, double TAUMOD_double, double TCOA_double, double DTHR_double, double TTHR_double, double ZTHR_double, double E_0_double, double E_1_double) {
  struct maybeBool res;
  double aux_0_double = vertical_WCV_exit_minus_entry_fp (B_double, T_double, sz_double, vz_double, TCOA_double, ZTHR_double);
  double aux_1_double = vertical_WCV_exit_minus_entry_fp (B_double, T_double, sz_double, vz_double, TCOA_double, ZTHR_double);
  double aux_2_double = vertical_WCV_exit_minus_entry_fp (B_double, T_double, sz_double, vz_double, TCOA_double, ZTHR_double);
  if (aux_0_double < - (E_0_double))
  { res = someBool(false);;
  }
  else if ((aux_0_double > E_0_double) && (aux_0_double >= E_0_double))
  { res = someBool(horizontal_WCV_taumod_interval_tauplus_bool(vertical_WCV_exit_minus_entry_fp (B_double, T_double, sz_double, vz_double, TCOA_double, ZTHR_double), B_double, B_double, vx_double, vy_double, TAUMOD_double, DTHR_double, E_1_double));; }
  else if ((aux_0_double <= - (E_0_double)) && (aux_0_double >= E_0_double))
  { res = someBool(false);; }
  else { res = noneBool();
  }
  return res;
}


/*@
assigns \nothing;
ensures \forall real B, real T, real sx, real sy, real sz, real vx, real vy, real vz, real TAUMOD, real TCOA, real DTHR, real TTHR, real ZTHR; (((((((((((((((((1 <= sx) && (sx <= 2)) && ((1 <= vx) && (vx <= 2))) && ((1 <= sy) && (sy <= 2))) && ((1 <= vy) && (vy <= 2))) && ((1 <= sz) && (sz <= 2))) && ((1 <= vz) && (vz <= 2))) && ((1 <= B) && (B <= 10))) && ((1 <= T) && (T <= 10))) && ((1 <= TAUMOD) && (TAUMOD <= 2))) && ((2 <= TCOA) && (TCOA <= 3))) && ((1 <= DTHR) && (DTHR <= 2))) && ((1 <= TTHR) && (TTHR <= 2))) && ((2 <= ZTHR) && (ZTHR <= 3))) && ((\result.isValid && ((((((((((((\is_finite(B_double) && \is_finite(T_double)) && \is_finite(sx_double)) && \is_finite(sy_double)) && \is_finite(sz_double)) && \is_finite(vx_double)) && \is_finite(vy_double)) && \is_finite(vz_double)) && \is_finite(TAUMOD_double)) && \is_finite(TCOA_double)) && \is_finite(DTHR_double)) && \is_finite(TTHR_double)) && \is_finite(ZTHR_double))) && ((((((((((((\abs(B_double - B) <= ulp_dp(B)/2 && \abs(T_double - T) <= ulp_dp(T)/2) && \abs(sx_double - sx) <= ulp_dp(sx)/2) && \abs(sy_double - sy) <= ulp_dp(sy)/2) && \abs(sz_double - sz) <= ulp_dp(sz)/2) && \abs(vx_double - vx) <= ulp_dp(vx)/2) && \abs(vy_double - vy) <= ulp_dp(vy)/2) && \abs(vz_double - vz) <= ulp_dp(vz)/2) && \abs(TAUMOD_double - TAUMOD) <= ulp_dp(TAUMOD)/2) && \abs(TCOA_double - TCOA) <= ulp_dp(TCOA)/2) && \abs(DTHR_double - DTHR) <= ulp_dp(DTHR)/2) && \abs(TTHR_double - TTHR) <= ulp_dp(TTHR)/2) && \abs(ZTHR_double - ZTHR) <= ulp_dp(ZTHR)/2)))
                                                                                                                                                 ==> ((\result.value
                                                                                                                                                       ==> (WCV_interval(B, T, sx, sy, sz, vx, vy, vz, TAUMOD, TCOA, DTHR, TTHR, ZTHR)))))) ;
*/
struct maybeBool WCV_interval_tauplus_num (double B_double, double T_double, double sx_double, double sy_double, double sz_double, double vx_double, double vy_double, double vz_double, double TAUMOD_double, double TCOA_double, double DTHR_double, double TTHR_double, double ZTHR_double) {
  return WCV_interval_tauplus_fp (B_double, T_double, sx_double, sy_double, sz_double, vx_double, vy_double, vz_double, TAUMOD_double, TCOA_double, DTHR_double, TTHR_double, ZTHR_double, 0x1p-52, 0x1.8000000000001p-50);
}




/*@ axiomatic WCV_interval_tauminus_trans {
predicate WCV_interval_tauminus_stable_paths (real B, real T, real sx, real sy, real sz, real vx, real vy, real vz, real TAUMOD, real TCOA, real DTHR, real TTHR, real ZTHR, double B_double, double T_double, double sx_double, double sy_double, double sz_double, double vx_double, double vy_double, double vz_double, double TAUMOD_double, double TCOA_double, double DTHR_double, double TTHR_double, double ZTHR_double) =
((((! ((vertical_WCV_exit_minus_entry(B, T, sz, vz, TCOA, ZTHR) > 0)) && ! ((vertical_WCV_exit_minus_entry(B, T, sz, vz, TCOA, ZTHR) < 0))) && ((! ((vertical_WCV_exit_minus_entry_fp(B_double, T_double, sz_double, vz_double, TCOA_double, ZTHR_double) > (double) (0))) && ! ((vertical_WCV_exit_minus_entry_fp(B_double, T_double, sz_double, vz_double, TCOA_double, ZTHR_double) < (double) (0)))) && (\true && \true))) || (((vertical_WCV_exit_minus_entry(B, T, sz, vz, TCOA, ZTHR) > 0) && ! ((vertical_WCV_exit_minus_entry(B, T, sz, vz, TCOA, ZTHR) < 0))) && (((vertical_WCV_exit_minus_entry_fp(B_double, T_double, sz_double, vz_double, TCOA_double, ZTHR_double) > (double) (0)) && ! ((vertical_WCV_exit_minus_entry_fp(B_double, T_double, sz_double, vz_double, TCOA_double, ZTHR_double) < (double) (0)))) && (\true && \true)))) || ((vertical_WCV_exit_minus_entry(B, T, sz, vz, TCOA, ZTHR) < 0) && ((vertical_WCV_exit_minus_entry_fp(B_double, T_double, sz_double, vz_double, TCOA_double, ZTHR_double) < (double) (0)) && (\true && \true))));
}
*/


/*@
requires ((0 <= E_0_double) && (0 <= E_1_double)) ;
assigns \nothing;

behavior structure:
ensures \forall real B, real T, real sx, real sy, real sz, real vx, real vy, real vz, real TAUMOD, real TCOA, real DTHR, real TTHR, real ZTHR; (((\result.isValid && ((((((((((((((\is_finite(B_double) && \is_finite(T_double)) && \is_finite(sx_double)) && \is_finite(sy_double)) && \is_finite(sz_double)) && \is_finite(vx_double)) && \is_finite(vy_double)) && \is_finite(vz_double)) && \is_finite(TAUMOD_double)) && \is_finite(TCOA_double)) && \is_finite(DTHR_double)) && \is_finite(TTHR_double)) && \is_finite(ZTHR_double)) && \is_finite(E_0_double)) && \is_finite(E_1_double)))
                                                                                                                                                 ==> ((\result.value
                                                                                                                                                       ==> ((! (WCV_interval(B, T, sx, sy, sz, vx, vy, vz, TAUMOD, TCOA, DTHR, TTHR, ZTHR)) && ! (WCV_interval_fp(B_double, T_double, sx_double, sy_double, sz_double, vx_double, vy_double, vz_double, TAUMOD_double, TCOA_double, DTHR_double, TTHR_double, ZTHR_double)))))))) ;

behavior stable_paths:
ensures \forall real B, real T, real sx, real sy, real sz, real vx, real vy, real vz, real TAUMOD, real TCOA, real DTHR, real TTHR, real ZTHR; (((\abs(vertical_WCV_exit_minus_entry_fp(B_double, T_double, sz_double, vz_double, TCOA_double, ZTHR_double) - vertical_WCV_exit_minus_entry(B, T, sz, vz, TCOA, ZTHR)) <= E_0_double && \abs(Dmul(DTHR_double, DTHR_double) - (DTHR * DTHR)) <= E_1_double)
                                                                                                                                                 ==> (((((((((((((((((\is_finite(B_double) && \is_finite(T_double)) && \is_finite(sx_double)) && \is_finite(sy_double)) && \is_finite(sz_double)) && \is_finite(vx_double)) && \is_finite(vy_double)) && \is_finite(vz_double)) && \is_finite(TAUMOD_double)) && \is_finite(TCOA_double)) && \is_finite(DTHR_double)) && \is_finite(TTHR_double)) && \is_finite(ZTHR_double)) && \is_finite(E_0_double)) && \is_finite(E_1_double)) && \result.isValid)
                                                                                                                                                       ==> (WCV_interval_tauminus_stable_paths(B, T, sx, sy, sz, vx, vy, vz, TAUMOD, TCOA, DTHR, TTHR, ZTHR, B_double, T_double, sx_double, sy_double, sz_double, vx_double, vy_double, vz_double, TAUMOD_double, TCOA_double, DTHR_double, TTHR_double, ZTHR_double)))))) ;
*/
struct maybeBool WCV_interval_tauminus_fp (double B_double, double T_double, double sx_double, double sy_double, double sz_double, double vx_double, double vy_double, double vz_double, double TAUMOD_double, double TCOA_double, double DTHR_double, double TTHR_double, double ZTHR_double, double E_0_double, double E_1_double) {
  struct maybeBool res;
  double aux_0_double = vertical_WCV_exit_minus_entry_fp (B_double, T_double, sz_double, vz_double, TCOA_double, ZTHR_double);
  double aux_1_double = vertical_WCV_exit_minus_entry_fp (B_double, T_double, sz_double, vz_double, TCOA_double, ZTHR_double);
  double aux_2_double = vertical_WCV_exit_minus_entry_fp (B_double, T_double, sz_double, vz_double, TCOA_double, ZTHR_double);
  if (aux_0_double < - (E_0_double))
  { res = someBool(true);;
  }
  else if ((aux_0_double > E_0_double) && (aux_0_double >= E_0_double))
  { res = someBool(horizontal_WCV_taumod_interval_tauminus_bool(vertical_WCV_exit_minus_entry_fp (B_double, T_double, sz_double, vz_double, TCOA_double, ZTHR_double), B_double, B_double, vx_double, vy_double, TAUMOD_double, DTHR_double, E_1_double));; }
  else if ((aux_0_double <= - (E_0_double)) && (aux_0_double >= E_0_double))
  { res = someBool(true);; }
  else { res = noneBool();
  }
  return res;
}


/*@
assigns \nothing;
ensures \forall real B, real T, real sx, real sy, real sz, real vx, real vy, real vz, real TAUMOD, real TCOA, real DTHR, real TTHR, real ZTHR; (((((((((((((((((1 <= sx) && (sx <= 2)) && ((1 <= vx) && (vx <= 2))) && ((1 <= sy) && (sy <= 2))) && ((1 <= vy) && (vy <= 2))) && ((1 <= sz) && (sz <= 2))) && ((1 <= vz) && (vz <= 2))) && ((1 <= B) && (B <= 10))) && ((1 <= T) && (T <= 10))) && ((1 <= TAUMOD) && (TAUMOD <= 2))) && ((2 <= TCOA) && (TCOA <= 3))) && ((1 <= DTHR) && (DTHR <= 2))) && ((1 <= TTHR) && (TTHR <= 2))) && ((2 <= ZTHR) && (ZTHR <= 3))) && ((\result.isValid && ((((((((((((\is_finite(B_double) && \is_finite(T_double)) && \is_finite(sx_double)) && \is_finite(sy_double)) && \is_finite(sz_double)) && \is_finite(vx_double)) && \is_finite(vy_double)) && \is_finite(vz_double)) && \is_finite(TAUMOD_double)) && \is_finite(TCOA_double)) && \is_finite(DTHR_double)) && \is_finite(TTHR_double)) && \is_finite(ZTHR_double))) && ((((((((((((\abs(B_double - B) <= ulp_dp(B)/2 && \abs(T_double - T) <= ulp_dp(T)/2) && \abs(sx_double - sx) <= ulp_dp(sx)/2) && \abs(sy_double - sy) <= ulp_dp(sy)/2) && \abs(sz_double - sz) <= ulp_dp(sz)/2) && \abs(vx_double - vx) <= ulp_dp(vx)/2) && \abs(vy_double - vy) <= ulp_dp(vy)/2) && \abs(vz_double - vz) <= ulp_dp(vz)/2) && \abs(TAUMOD_double - TAUMOD) <= ulp_dp(TAUMOD)/2) && \abs(TCOA_double - TCOA) <= ulp_dp(TCOA)/2) && \abs(DTHR_double - DTHR) <= ulp_dp(DTHR)/2) && \abs(TTHR_double - TTHR) <= ulp_dp(TTHR)/2) && \abs(ZTHR_double - ZTHR) <= ulp_dp(ZTHR)/2)))
                                                                                                                                                 ==> ((\result.value
                                                                                                                                                       ==> (! (WCV_interval(B, T, sx, sy, sz, vx, vy, vz, TAUMOD, TCOA, DTHR, TTHR, ZTHR))))))) ;
*/
struct maybeBool WCV_interval_tauminus_num (double B_double, double T_double, double sx_double, double sy_double, double sz_double, double vx_double, double vy_double, double vz_double, double TAUMOD_double, double TCOA_double, double DTHR_double, double TTHR_double, double ZTHR_double) {
  return WCV_interval_tauminus_fp (B_double, T_double, sx_double, sy_double, sz_double, vx_double, vy_double, vz_double, TAUMOD_double, TCOA_double, DTHR_double, TTHR_double, ZTHR_double, 0x1p-52, 0x1.8000000000001p-50);
}


int main () { return 0; }