#include<stdbool.h>

#define round(X) (double) (X)

/*@
  logic double Dadd(double X, double Y) = round(X+Y);

  logic double Dsub(double X, double Y) = round(X-Y);

  logic double Dmul(double X, double Y) = round(X*Y);

  logic double Dneg(double X) = round(-X);

  logic double Dabs(double X) = round(X);

  logic double Ddiv(double X, double Y) = (Y != round(0.0) ? round(X/Y) : round(0.0));

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

axiomatic axioms{
  predicate Dadd_ov(double X, double Y);
  predicate Dsub_ov(double X, double Y);
  predicate Dmul_ov(double X, double Y);
  predicate Ddiv_ov(double X, double Y);
  predicate Dneg_ov(double X);
  predicate Dabs_ov(double X);

  axiom Dadd_ov_def:
    \forall double X, Y;
      Dadd_ov(X, Y) <==> (!\is_finite(Dadd(X, Y)) || !\is_finite(X) || !\is_finite(Y));

  axiom Dsub_ov_def:
    \forall double X, Y;
      Dsub_ov(X, Y) <==> (!\is_finite(Dsub(X, Y)) || !\is_finite(X) || !\is_finite(Y));

  axiom Dmul_ov_def:
    \forall double X, Y;
      Dmul_ov(X, Y) <==> (!\is_finite(Dmul(X, Y)) || !\is_finite(X) || !\is_finite(Y));

  axiom Ddiv_ov_def:
    \forall double X, Y;
      Ddiv_ov(X, Y) <==> (!\is_finite(Ddiv(X, Y)) || !\is_finite(X) || !\is_finite(Y));

  axiom Dneg_ov_def:
    \forall double X, Y;
      Dneg_ov(X) <==> (!\is_finite(Dneg(X)) || !\is_finite(X));

  axiom Dabs_ov_def:
    \forall double X, Y;
      Dabs_ov(X) <==> (!\is_finite(Dabs(X)) || !\is_finite(X));
}
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