--Ostrich
--Aneesh: akv6zr
--Asad: as9vd
  
/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/
--example : true := _

example : true := true.intro

--example : false := _    -- trick question? why?


/-
Assuming P is an object of type Prop, and that P ∨ P is true with porp, we
can apply the or elimination rule to porp to break the proposition into two smaller propositions. 
For the forward direction, we assumed we had a proof of P ∨ P, and created a case analysis. 
In both cases, we proved that we had a proof of P, so P ∨ P → P. In the backwards direction, 
we assumed we had a proof of P, and then we used the or left introduction rule to demonstrate that
P → P ∨ P. We then combine these two proofs to prove the ↔ statement. QED. -/

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  --forward
  assume porp,
  apply or.elim porp,
--left disjunct is true
  assume P,
  exact P,
--right disjunct is true
  assume P,
  exact P,
--backward
  assume p,
  exact or.intro_left P p,
  assume P, 
  apply iff.intro _ _,
  -- forward
    assume porp,
    apply or.elim porp,
    -- left disjunct is true
      assume p,
      exact p,
    -- right disjunct is true
      assume p,
      exact p,
  -- backwards
    assume p,
    exact or.intro_left P p,
end

/- Assuming we have an object P of type Prop, we can split this statement up into both forwards and backwards cases.
If we assume P ∧ P is true, the elimination rule of 'and' helps us deduce that P is true. Therefore, we can apply
this fact and prove that P ∧ P implies P. As for the backwards direction, if we split up P ∧ P into
individual propositions, we can apply the assumed true proposition P to each bit. We then combine these two 
proofs to prove the ↔ statement. QED. -/

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,

  assume pandp,
  apply and.elim pandp,
  assume p,
  assume p,
  exact p, --exact means use the proof that we provide as an argument

  assume P,
  apply and.intro _ _,
  exact P,
  exact P,
end

/- Assuming we have an object P and Q of type Prop, we can split this statement up into both forwards and backwards cases.
For the forward direction, we assume that the proof P ∨ Q was true, and then we apply the or elimination rule to the proof
in order to prove Q ∨ P. Then, for the backward direction, we assume a proof of Q ∨ P, and then using the symmetric property of
equality (in this case, or.swap), we mirrored Q ∨ P to display P ∨ Q, which proves the proposition P ∨ Q. We then combine these two
proofs to prove the ↔ statement. QED. -/


example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q,
  apply iff.intro _ _,

  assume porq,
  apply or.elim porq,

  assume p,
  apply or.swap porq,
 
 assume q,
 apply or.swap porq,

 assume qorp,
 apply or.swap qorp,

end

/- Assuming P and Q are two objects of type Prop, we can break this ↔ statement
into two separate proofs. Assuming P ∧ Q is true, we can apply the symmetry property
of equality (and.swap in this case) to both sides and prove that P ∧ Q → Q ∧ P. 
For the backwards case, the same exact steps are taken. We then combine these two
proofs to prove the ↔ statement. QED. -/

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro _ _,

  assume pandq,
  apply and.swap pandq,

  assume qandp,
  apply and.swap qandp,
end

/- Assuming P, Q, and R are three objects of type Prop, we can break this ↔ statement
into two separate proofs. First, we assume we are given the proof P ∧ (Q ∨ R) for the 
forward direction. Via case analysis, we can split the proof up into smaller bits P and Q ∨ R.
Via more case analysis, we can split the right proof up to Q and R individually. Applying the 
or left introduction rule to the proof, we get a smaller proof of P ∧ Q, and using the and introduction rule,
we can apply proofs P and Q to the broken up proof of P ∧ Q. Then, for case 2, we use the or right introduction
rule to prove P ∨ R. Using the and introduction rule, we can apply our smaller proofs of P and R individually to prove
P ∨ R. This wraps up the forward direction. As for the backward direction, we assume a proof of 
(P ∧ Q) ∨ (P ∧ R). Then, two consecutive case analyses are done on this proof, breaking
the statements into smaller pieces and applying P and Q individually to statements broken up using
the and introduction rule. Finally, using the or right introduction rule, we split Q ∨ R into R, which is proven
with the given proof of R we assumed. We then combine these two proofs to prove the ↔ statement. QED. -/

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,
  assume paqor,

  cases paqor,
  cases paqor_right,
  apply or.intro_left,
  apply and.intro,
  apply paqor_left,
  apply paqor_right,

  apply or.intro_right,
  apply and.intro,
  apply paqor_left,
  apply paqor_right,

  assume paqopor,
  cases paqopor,
  cases paqopor,
  apply and.intro,

  apply paqopor_left,
  apply or.intro_left,
  apply paqopor_right,

  cases paqopor,
  apply and.intro,
  apply paqopor_left,
  apply or.intro_right,
  apply paqopor_right,
end

/- Assuming P, Q, and R are three objects of type Prop, we can break this ↔ statement
into two separate proofs. First, we assume that P ∨ (Q ∧ R) is true. Using case analysis,
we broke this down into two proofs of P and Q ∨ R. Firstly, we applied the and introdction
rule to split the proof up. Then, using the or left introduction rule, we broke P ∨ Q down into
P, which we proved using our proof of P. P ∧ R required the usage of the same or left introduction
rule, which we proved with our proof of P as well. To prove (P ∨ Q) ∧ (P ∨ R) with our proof of
Q ∧ R, we broke Q ∧ R into cases. We then applied the or right introduction rule to turn P ∨ Q into
Q, which was proved with our proof of Q. The same steps were taken for P ∨ R.
As for the forward statement, assuming (P ∨ Q) ∧ (P ∨ R), we broke this down using case analysis.
In case 1, we created another case analysis of P ∨ Q. Using the or introduction rule, 
we got P from P ∨ Q ∧ R, which we proved using our proof of P. Then, for case 2, we did further
analysis of P ∧ R. Applying the or introduction rule, we got Q ∧ R. Then, using the and introduction rule,
we split this up into propositions Q and R, which we solved using the proofs we had
for Q and R. We then combined these two proofs to prove the ↔ statement. QED. -/

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
assume P Q R,
apply iff.intro _ _,
assume paqor,
cases paqor,
apply and.intro,
apply or.intro_left,
apply paqor,
apply or.intro_left,
apply paqor,

apply and.intro,
cases paqor,
apply or.intro_right,
apply paqor_left,

cases paqor,
apply or.intro_right,
apply paqor_right,

assume poqapor,
cases poqapor,
cases poqapor_left,
apply or.intro_left,
apply poqapor_left,

cases poqapor_right,
apply or.intro_left,
apply poqapor_right,
apply or.intro_right,
apply and.intro,
apply poqapor_left,
apply poqapor_right,
end

/- Assuming objects P and Q are of type Prop, we can break this double-arrowed statement into two
goals to prove. To prove P and (P or Q) is equal to P, you can use and's elimination rule to demonstrate
that P is true. Then, for the backwards portion of the proof, you can split the left half of the proposition to prove
each part individually. P does imply P, as per the reflexivity axiom of equality,
Then, breaking up P ∨ Q into P allows us to apply P to prove P.
We then combined these two proofs to prove the ↔ statement. QED. -/

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,

  assume p,
  apply and.elim_left p,

  assume p,
  split,

  apply p,
  apply or.inl,
  exact p,
end


/- Assuming P and Q are objects of type Prop, we can break this ↔ statement
into two separate proofs. First, we assume P ∨ (P ∧ Q) is true. Using 
case analysis, we need to prove P using proofs of P and P ∧ Q. The first one was
simple, as we just had to apply P. The second case requires the usage of the and elimination rule to
P ∧ Q in order to prove P. As for the backwards case, assuming P is true, we can apply
the or left introduction rule to p of type (P ∧ Q), which proves the validity of P.
We then combined these two proofs to prove the ↔ statement. QED. -/

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
assume P Q,
apply iff.intro _ _,
assume porpandq,
cases porpandq,
exact porpandq,

apply and.elim_left porpandq,

assume p,
apply or.intro_left (P ∧ Q) p,
end

/- Assuming P is an object of type Prop, we can break this ↔ statement
into two separate proofs. Assuming P ∨ true, we can use the or elimination rule to
split the proof up into P → true and true → true. Doing a case analysis,
we can apply the true introduction rule (true.intro) to both cases, which proves
P ∧ true. As for the backward statement, we applied the or right introduction rule (or.intro_right)
to true, which we applied in order to prove that true → P ∨ true.
We then combined these two proofs to prove the ↔ statement. QED. -/

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro _ _,

  assume port,
  apply or.elim port,
  cases port,
  
  assume p,
  apply true.intro,
  assume p,
  apply true.intro,

  cases port,
  assume p,
  apply true.intro,
  assume p,
  apply true.intro,

  assume t,
  apply or.intro_right P t,

end

/- Assuming P is an object of type Prop, we can break this ↔ statement into two separate proofs.
Given P ∨ false, we use the or elimination rule to break the proofs up. Then, having broken the proofs up,
we do case analysis on each individual proof, and we apply P to each proof. Then, we do a case analysis
of false to prove that P ∨ false → P. Afterward, for the second proof, we assumed a proof of P to solve
P ∨ false. Applying or.inl, we turned P ∨ false into P, which was proven with our assumed proof of P. 
We then combined these two proofs to prove the ↔ statement. QED. -/

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume p,
  apply iff.intro _ _,
  assume porf,
  apply or.elim porf,

  cases porf,
  assume p,
  exact p,
  assume p,
  exact p,

  assume false,
  cases false,
  assume p,
  apply or.inl,
  exact p,
end

/- Assuming P is an object of type Prop, we can break this ↔ statement
into two separate proofs. In the first proof, we assume P ∧ true is true. Applying
the and left elimination rule (and.elim_left) to this statement, we get a proof of P.
As for the backward direction, we assume P is true. Applying the introduction rule to 
P ∧ true, we split the statement up into two separate proofs. For the first one, we apply
our proof of P, and for the second, we use the true introduction rule to prove that true = true. 
We then combined these two proofs to prove the ↔ statement. QED. -/

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
  assume pandt,
  apply and.elim_left pandt,

  assume p,
  apply and.intro,
  exact p,
  exact true.intro,
end

/- Assuming P is an object of type Prop, we can break this ↔ statement
into two separate proofs. Assuming P ∧ false, we can do a case analysis on this proof.
We apply false to false, which yields us false. However, in the backward statement, we assume
false, and doing a case analysis on false yields us an arbitrary proof. We then combined
these two proofs to prove the ↔ statement. QED. -/

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume p,
  apply iff.intro _ _,
  assume pandf,
  
  cases pandf with p false,
  cases false,
  assume false,
  cases false with p q,
end


