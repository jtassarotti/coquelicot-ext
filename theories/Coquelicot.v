(**
This library provides vernacular files containing a formalization of real
analysis for Coq. It is a conservative extension of the standard library Reals
with a focus on usability. It has been developed by Sylvie Boldo, Catherine
Lelay, and Guillaume Melquiond.

The goal of Coquelicot is to ease the writing of formulas and theorem statements
for real analysis. This is achieved by using total functions in place of
dependent types for limits, derivatives, integrals, power series, and so on.
To help with the proof process, the library comes with a comprehensive set
of theorems that cover not only these notions, but also some extensions such
as parametric integrals, two-dimensional differentiability, asymptotic
properties. It also offers some automations for performing differentiability
proofs. Since Coquelicot is a conservative extension of Coq's standard
library, we provide correspondence theorems between the two libraries.


* Main types


- [R]: the set of real numbers defined by Coq's standard library.
- [Rbar]: [R] extended with signed infinities [p_infty] and [m_infty]. There is
  a coercion from [R] to [Rbar].
- [C]: the set of complex numbers, defined as pairs of real numbers. There is a
  coercion from [R] to [C].
- [@matrix T m n]: matrices with m rows and n columns of coefficients of type T.


* Main classes


- [UniformSpace]: a uniform space with a predicate [ball] defining an ecart.
- [CompleteSpace]: a [UniformSpace] that is also complete.
- [AbelianGroup]: a type with a commutative operator [plus] and a neutral
  element [zero]; elements are invertible ([opp], [minus]).
- [Ring]: an [AbelianGroup] with a noncommutative operator [mult] that is
  distributive with respect to [plus]; [one] is the neutral element of [mult].
- [AbsRing]: a [Ring] with an operator [abs] that is subdistributive
  with respect to [plus] and [mult].
- [ModuleSpace]: an [AbelianGroup] with an operator [scal] that defines a
  left module over a [Ring].
- [NormedModule]: a [ModuleSpace] that is also a [UniformSpace]; it provides an
  operator [norm] that defines the same topology as [ball].
- [CompleteNormedModule]: a [NormedModule] that is also a [CompleteSpace].


In the following definitions, K will designate either a [Ring] or an [AbsRing],
while U and V will designate a [ModuleSpace], a [NormedModule], or a
[CompleteNormedModule].


* Low-level concepts of topology


Limits and neighborhoods are expressed in terms of filters, that is, predicates
of type [(T -> Prop) -> Prop]. Sets from a filter are stable by intersection and
extension. Filters are used to describe limit points and how they are approached.
The properties of a filter are described by the [Filter] record. If a filter
does not contain the empty set, it is also a [PerfectFilter].


In a [UniformSpace], [ball x eps y] states that y lies in a ball of center x and
radius eps. [locally x] is the filter generated by all the balls of center x. As
such, its single limit point is x. Thus [locally x] matches the traditional notion
of convergence toward [x] in a metric space. Note: [locally x] is also the set of
neighborhoods of x.


The supported filters are as follows:
- [locally x].
- [locally' x] is similar to [locally x], except that x is missing from every
  set. Thus, while its limit point is x too, properties at point x do not
  matter.
- [Rbar_locally x] is defined for x in [Rbar]. It is [locally x] if x is finite,
  otherwise it is the set of half-bounded open intervals extending to either
  [m_infty] or [p_infty], depending on which infinity x is. In the latter case,
  the limit described by the filter is plus or minus infinity.
- [Rbar_locally' x] is to [Rbar_locally x] what [locally' x] is to [locally x].
- [at_left x] restricts the balls of [locally x] to points strictly less
  than x, thus properties of points on the right of x do not matter.
- [at_right x] is analogous to [at_left x] and is used to take limits on the right.
- [filter_prod G H] is a filter describing the neighborhoods of point (g,h) if
  G describes the neighborhoods of g while H describes the neighborhoods of h.
- [eventually] is a filter on natural numbers that converges to plus infinity.
- [within dom F] weakens a filter F by only considering points that satisfy dom.


Examples:
- [locally x P] can be interpreted in several ways depending on the meaning of P.
  As a set, it means that P contains a ball centered at x, that is, P is a
  neighborhood of x. As a predicate, it means that P holds on a neighborhood of x.
- [locally 2 (fun x => 0 < ln x)] means that [ln] has positive values in
  a neighborhood of 2.
- [at_left 1 (fun x => -1 < ln x < 0)] means that [ln] has values between -1
  and 0 in the left part of a neighborhood of 1.


Open sets are described by the [open] predicate. It states that a set is open
if it is a neighborhood of any of its points (in terms of [locally]). Closed sets
are described by [closed].


* Limits and continuity


Limits and continuity are expressed with filters using predicate [filterlim :
(S -> T) -> ((S -> Prop) -> Prop) -> ((T -> Prop) -> Prop)]. Property
[filterlim f K L] means that the preimage of any set of L by f is a set of K.
In other words, function f, at the limit point described by filter K tends to
the limit point described by filter L.


Examples:
- [filterlim f (locally x) (locally (f x))] means that f is continuous
  at point x. [filterlim f (locally' x) (locally (f x))] is another way to state
  it, since x is necessarily in the preimage of f x and thus can be ignored.
- [filterlim f (at_right x) (locally y)] means that f t tends to y when t tends
  to x from the right.
- [filterlim exp (Rbar_locally m_infty) (at_right 0)] means that [exp] tends
  to 0 at minus infinity but only takes positive values there.
- [forall x y : R, filterlim (fun z => fst z + snd z) (filter_prod (locally x)
  (locally y)) (locally (x + y))] states that [Rplus] is continuous.


Lemma [filterlim_locally] gives the traditional epsilon-delta definition of
continuity. Compatibility with the [continuity_pt] predicate from the standard
library is provided by lemmas such as [continuity_pt_filterlim].


The following predicates specialize [filterlim] to the usual cases of
real-valued sequences and functions:
- [is_lim_seq : (nat -> R) -> Rbar -> Prop], e.g. [is_lim_seq (fun n => 1 + /
  INR n) 1].
- [is_lim : (R -> R) -> Rbar -> Rbar -> Prop], e.g. [is_lim exp p_infty
  p_infty].


The unicity of the limits is given by lemmas [is_lim_seq_unique] and
[is_lim_unique]. The compatibility with the arithmetic operators is given
by lemmas such as [is_lim_seq_plus] and [is_lim_seq_plus']. They are
derived from the generic lemmas [filterlim_plus] and [filterlim_comp_2].


Lemmas [is_lim_seq_spec] and [is_lim_sprec] gives the traditional epsilon-delta
definition of convergence. Compatibility with the [Un_cv] and [limit1_in]
predicates from the standard library is provided by lemmas [is_lim_seq_Reals]
and [is_lim_Reals].


When only the convergence matters but not the actual value of the limit, the
following predicates can be used instead, depending on whether the value can
be infinite or not:
- [ex_lim_seq : (nat -> R) -> Prop].
- [ex_lim : (R -> R) -> Rbar -> Prop].
- [ex_finite_lim_seq : (nat -> R) -> Prop].
- [ex_finite_lim : (R -> R) -> Rbar -> Prop].


Finally, there are also some total functions that are guaranteed to return the
proper limits if the sequences or functions actually converge:
- [Lim_seq : (nat -> R) -> Rbar], e.g. [Lim_seq (fun n => 1 + / INR n)] is equal
  to 1.
- [Lim : (R -> R) -> Rbar -> Rbar].


If they do not converge, the returned value is arbitrary and no interesting
results can be derived. These functions are related to the previous predicates
by lemmas [Lim_seq_correct] and [Lim_correct].


As with predicates [filterlim], [is_lim_seq], and [is_lim], compatibility with
the arithmetic operators is given by lemmas such as [ex_lim_seq_mult] and
[Lim_inv].


Compatibility with predicates [Un_cv] and [limit1_in] from the standard library
is provided by lemmas [is_lim_seq_Reals] and [is_lim_Reals].


* Derivability and differentiability


The predicate of differentiability is [filterdiff : (U -> V) -> ((U -> Prop) ->
Prop) -> (U -> V) -> Prop]. Property [filterdiff f K l] means that, at the
limit point described by filter K, the differential of function f is the linear
function l. Linearity is described by the predicate [is_linear].


While [filterdiff_ext] states that two functions extensionally equal have the
same differential, [filterdiff_ext_lin] states that the differential can be
replaced by any linear function that is extensionally equal.


When the domain space of the function is an [AbsRing] rather than just a
[NormedModule] and the filter is [locally], the following specialized predicates
can be used instead:
- [is_derive : (K -> V) -> K -> V -> Prop].
- [ex_derive : (K -> V) -> K -> V -> Prop].


For real-valued functions, the following total function gives the value of the
derivative, if it exists: [Derive : (R -> R) -> R -> R]. The specification of
this function is given by lemma [Derive_correct]. Compatibility of the
predicates with [derivable_pt_lim] from the standard library is given by
[is_derive_Reals].


Tactic [auto_derive] can be used to automatically solve goals about [is_derive],
[ex_derive], [derivable_pt_lim], and [derivable_pt].


* Riemann integrals


The main predicate is [is_RInt : (R -> V) -> R -> R -> V -> Prop]. [is_RInt f a
b l] means that the Riemann sums of function f between a and b converge and
their limit is equal to l. This is a specialization of [filterlim] for a
function built using [Riemann_sum] and the [Riemann_fine] filter.


As before, there are a predicate and a total function related to it:
- [ex_RInt : (R -> V) -> R -> R -> Prop].
- [RInt : (R -> R) -> R -> R -> R].


Compatibility with predicate [Riemann_integrable] from the standard library is
provided by lemmas [ex_RInt_Reals_0] and [ex_RInt_Reals_1].


* Series and power series


The main predicates are [is_series : (nat -> V) -> V -> Prop] and [is_pseries :
(nat -> V) -> K -> V -> Prop].


The associated predicates and functions are as follows:
- [ex_series : (nat -> V) -> Prop].
- [ex_pseries : (nat -> V) -> K -> Prop].
- [Series : (nat -> R) -> R].
- [PSeries : (nat -> R) -> R -> R].


There is also a function [CV_radius : (nat -> R) -> Rbar] that returns the
possibly infinite convergence radius.


Compatibility with predicates [infinite_sum] and [Pser] from the standard
library is provided by lemmas [is_series_Reals] and [is_pseries_Reals].


* Naming conventions


- Theorems about a given predicate start with its name, generally followed
  by the name of the object it is applied to, e.g. [is_RInt_plus], or a property
  of the object, e.g. [filterdiff_linear].
- Correspondence theorems with the standard library end with [_Reals].
- Extensionality theorems end with [_ext]. If the equality only needs to
  be local, they end with [_ext_loc] instead.
- Uniqueness theorems end with [_unique].
- Theorems about asymptotic properties at plus, resp. minus, infinity end with
  [_p], resp. [_m].
  if they are at infinite points.
- Theorems about constant functions, resp. identity, end with [_const], resp.
  [_id].

*)

Require Export AutoDerive Compactness Complex Continuity Derive.
Require Export Derive_2d Equiv ElemFct Hierarchy Lim_seq.
Require Export Lub Markov PSeries Rbar Rcomplements.
Require Export RInt Seq_fct Series SF_seq.

(** #<img src="deps.png" usemap="##coquelicot_deps" /># *)

(**
This file is part of the Coquelicot formalization of real
analysis in Coq: http://coquelicot.saclay.inria.fr/

Copyright (C) 2011-2015 Sylvie Boldo
#<br />#
Copyright (C) 2011-2015 Catherine Lelay
#<br />#
Copyright (C) 2011-2015 Guillaume Melquiond

This library is free software; you can redistribute it and/or
modify it under the terms of the GNU Lesser General Public
License as published by the Free Software Foundation; either
version 3 of the License, or (at your option) any later version.

This library is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
COPYING file for more details.
*)
