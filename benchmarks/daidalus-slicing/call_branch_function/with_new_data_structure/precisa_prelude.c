#include<stdbool.h>

#define round(X) (double) (X)

//@ ghost struct doubleOV { double value; bool overflow; };

//@ type double_ov = struct doubleOV ;

/*@
axiomatic fp_ops{
    logic double_ov empty;

    logic double_ov DoubleOV(double X);

    axiom DoubleOV_def:
      \forall double X;
        DoubleOV(X).value == X &&
        (( \is_finite(X) && !DoubleOV(X).overflow) ||
         (!\is_finite(X) && DoubleOV(X).overflow));

    logic double_ov Dadd(double_ov X, double_ov Y);
    logic double_ov Dsub(double_ov X, double_ov Y);
    logic double_ov Dmul(double_ov X, double_ov Y);
    logic double_ov Ddiv(double_ov X, double_ov Y);
    logic double_ov Dneg(double_ov X);
    logic double_ov Dabs(double_ov X);

    logic double_ov Dif(double_ov arg, double_ov true_result,  double_ov false_result);

    axiom Dif_value_def:
      \forall double_ov arg, true_result, false_result;
        Dif(arg, true_result, false_result).value == ((arg.value < (double) 0)? true_result.value : false_result.value);

    axiom Dif_overflow_def:
      \forall double_ov arg, true_result, false_result;
        (Dif(arg, true_result, false_result).overflow == arg.overflow? true : ((arg.value < (double) 0)? true_result.overflow : false_result.overflow));

    axiom Dadd_value_def:
        \forall double_ov X,Y;
            Dadd(X, Y).value == round(X.value + Y.value);

    axiom Dadd_overflow_def:
       \forall double_ov X,Y;
          ( \is_finite(Dadd(X, Y).value) && Dadd(X, Y).overflow == (X.overflow || Y.overflow)) ||
          (!\is_finite(Dadd(X, Y).value) && Dadd(X, Y).overflow);

    axiom Dsub_value_def:
        \forall double_ov X,Y;
            Dsub(X, Y).value == round(X.value - Y.value);

    axiom Dsub_overflow_def:
       \forall double_ov X,Y;
          ( \is_finite(Dsub(X, Y).value) && Dsub(X, Y).overflow == (X.overflow || Y.overflow)) ||
          (!\is_finite(Dsub(X, Y).value) && Dsub(X, Y).overflow);

    axiom Dmul_value_def:
        \forall double_ov X,Y;
            Dmul(X, Y).value == round(X.value * Y.value);

    axiom Dmul_overflow_def:
       \forall double_ov X,Y;
          ( \is_finite(Dmul(X, Y).value) && Dmul(X, Y).overflow == (X.overflow || Y.overflow)) ||
          (!\is_finite(Dmul(X, Y).value) && Dmul(X, Y).overflow);

    axiom Ddiv_value_def:
        \forall double_ov X,Y;
            Ddiv(X, Y).value == (Y.value != round(0.0) ? round(X.value/Y.value) : round(0.0));

    axiom Ddiv_overflow_def:
       \forall double_ov X,Y;
          ( \is_finite(Ddiv(X, Y).value) && Ddiv(X, Y).overflow == (X.overflow || Y.overflow)) ||
          (!\is_finite(Ddiv(X, Y).value) && Ddiv(X, Y).overflow);

    axiom Dneg_value_def:
        \forall double_ov X;
            Dneg(X).value == round(-X.value);

    axiom Dneg_overflow_def:
       \forall double_ov X;
          ( \is_finite(Dneg(X).value) && Dneg(X).overflow == X.overflow) ||
          (!\is_finite(Dneg(X).value) && Dneg(X).overflow);
}
*/

/*@

logic integer Iadd(integer X, integer Y) = X+Y;

logic integer Isub(integer X, integer Y) = X-Y;

logic integer Imul(integer X, integer Y) = X*Y;

logic integer Ineg(integer X) = 0-X;

logic real ulp_dp(real X) = \round_double(\Up,X)-\round_double(\Down,X);

logic real errAdd_dp(real X, real E_X, real Y, real E_Y)
= E_X + E_Y + ulp_dp(\abs(X + Y) + E_X + E_Y)/2;

logic real errSub_dp(real X, real E_X, real Y, real E_Y)
= E_X + E_Y + ulp_dp(\abs(X - Y) + E_X + E_Y)/2;

logic real errMul_dp(real X, real E_X, real Y, real E_Y)
= \abs(X)*E_Y+\abs(Y)*E_X+E_X*E_Y + ulp_dp(\abs(X)*\abs(Y) + \abs(X)*E_Y + E_X*\abs(Y) + E_X*E_Y)/2;

logic real errDiv_dp(real X, real E_X, real Y, real E_Y)
= ( ((Y*Y - E_Y*\abs(Y)) != 0 && (\abs(Y) - E_Y) !=0)? (\abs(Y)*E_X + \abs(X)*E_Y) / (Y*Y - E_Y*\abs(Y)) + ulp_dp((\abs(X) + E_X) / (\abs(Y) - E_Y)) / 2 : 0 );

logic real errNeg_dp(real X, real E_X) = E_X;

logic real errAdd_i(integer X, real E_X, integer Y, real E_Y) = E_X + E_Y;

logic real errSub_i(integer X, real E_X, integer Y, real E_Y) = E_X + E_Y;
*/

struct maybeInt {
  bool isValid;
  int value;
};

/*@ assigns \nothing;
ensures ! \result.isValid;
*/
struct maybeInt none () {
  struct maybeInt result = { false, 0 };
  return result;
}

/*@ assigns \nothing;
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

/*@ assigns \nothing;
ensures ! \result.isValid;
*/
struct maybeFloat noneFloat () {
  struct maybeFloat result = { false, 0 };
  return result;
}

/*@ assigns \nothing;
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

/*@ assigns \nothing;
ensures ! \result.isValid;
*/
struct maybeDouble noneDouble () {
  struct maybeDouble result = { false, 0 };
  return result;
}

/*@ assigns \nothing;
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

/*@ assigns \nothing;
ensures \result.isValid;
ensures \result.value == val;
*/
struct maybeBool someBool (bool val) {
  struct maybeBool result = { true, val };
  return result;
}