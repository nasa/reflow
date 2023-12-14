#include<stdbool.h>

#define round(X) (double) (X)

#define emin_sp -126
#define p_sp 24

#define emin_dp -1022
#define p_dp 53
#define BASE 2

/*@
logic double Dadd(double X, double Y) = \add_double(X, Y);

logic double Dsub(double X, double Y) = \sub_double(X, Y);

logic double Dmul(double X, double Y) = \mul_double(X, Y);

logic double Dneg(double X) = \neg_double(X);

logic double Ddiv(double X, double Y) = \div_double(X, Y);

logic double Dsqrt(double X) = sqrt(X);

axiomatic comp{
  logic bool Dgt(double X, double Y);
  logic bool Dge(double X, double Y);
  logic bool Dlt(double X, double Y);
  logic bool Dle(double X, double Y);
  logic bool Dne(double X, double Y);
  logic bool Deq(double X, double Y);

  axiom Dgt_def:
      \forall double X, Y;
        !Dgt(X, Y) <==> !\gt_double(X, Y);

  axiom Dge_def:
      \forall double X, Y;
        !Dge(X, Y) <==> !\ge_double(X, Y);

  axiom Dlt_def:
      \forall double X, Y;
        !Dlt(X, Y) <==> !\lt_double(X, Y);

  axiom Dle_def:
      \forall double X, Y;
        !Dle(X, Y) <==> !\le_double(X, Y);

   axiom Dne_def:
      \forall double X, Y;
        !Dne(X, Y) <==> !\ne_double(X, Y);

   axiom Deq_def:
      \forall double X, Y;
        !Deq(X, Y) <==> !\eq_double(X, Y);
}

predicate equal_fp(double instrumented, double notInstrumented) =
  \is_NaN(instrumented)? \is_NaN(notInstrumented): \eq_double(instrumented, notInstrumented);

logic double Dabs(double X) = Deq(X, (double) 0.0)? Dmul((double) 0.0, (double) 0.0): (Dlt(X, (double)0)? \neg_double(X):X);

logic integer Iadd(integer X, integer Y) = X+Y;

logic integer Isub(integer X, integer Y) = X-Y;

logic integer Imul(integer X, integer Y) = X*Y;

logic integer Ineg(integer X) = 0-X;

logic real ulp_dp(real x) = (x == 0)? \pow(BASE, (emin_dp - p_dp + 1)) :  \pow(BASE, (\max(\floor(\log(\abs(x))/\log(2)), emin_dp) - p_dp + 1));

*/

struct maybeInt {
  bool isValid;
  int value;
};

/*@ 
 assigns \nothing;
 ensures ! \result.isValid;
 */
struct maybeInt none () {
  struct maybeInt result = { false, 0 };
  return result;
}

/*@
 assigns \nothing;
 ensures \result.isValid;
 ensures \result.value == val;
 */
struct maybeInt some (int val) {
  struct maybeInt result = { true, val };
  return result;
}

struct maybeFloat {
  bool isValid;
  float value;
};

/*@ 
 assigns \nothing;
 ensures ! \result.isValid;
 */
struct maybeFloat noneFloat () {
  struct maybeFloat result = { false, 0 };
  return result;
}

/*@ 
 assigns \nothing;
 ensures \result.isValid;
 ensures \result.value == val;
 */
struct maybeFloat someFloat (float val) {
  struct maybeFloat result = { true, val };
  return result;
}

struct maybeDouble {
  bool isValid;
  double value;
};

/*@ 
 assigns \nothing;
 ensures ! \result.isValid;
 */
struct maybeDouble noneDouble () {
  struct maybeDouble result = { false, 0 };
  return result;
}

/*@ 
 assigns \nothing;
 ensures \result.isValid;
 ensures \result.value == val;
 */
struct maybeDouble someDouble (double val) {
  struct maybeDouble result = { true, val };
  return result;
}

struct maybeBool {
  bool isValid;
  bool value;
};

/*@
 assigns \nothing;
 ensures ! \result.isValid;
 */
struct maybeBool noneBool () {
  struct maybeBool result = { false, false };
  return result;
}

/*@ 
 assigns \nothing;
 ensures \result.isValid;
 ensures \result.value == val;
 */
struct maybeBool someBool (bool val) {
  struct maybeBool result = { true, val };
  return result;
}

/*@ 
 ensures equal_fp(\result, Dabs(x));
 assigns \nothing;
 */
double precisa_prelude_fabs(double x){
  return ((x == 0.0)? 0.0*0.0: ((x < 0)? -x: x));
}

#define fabs(X) precisa_prelude_fabs(X)
