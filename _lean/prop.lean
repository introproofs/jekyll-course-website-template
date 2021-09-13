-- At its core, Lean is what is known as a type checker. This means that we can write expressions and ask the system to check that they are well formed, and also ask the system to tell us what type of object they denote.

-- Lean installation guide: https://leanprover-community.github.io/get_started.html

-- alternatively, use the web editor: https://leanprover-community.github.io/lean-web-editor/#


-- try prop, what error do you get?

variables P Q R : Prop

#check P 
#check Q → R 

-- error?
#check P ∧ A 
#check P ∧ Q 


-- no need for commas for many variables 
variables A B : Prop 

-- The way to tell Lean that a hypothesis is true.
variable h : A ∧ ¬ B
#check h 

-- conjunction elim
#check and.left h 
#check and.right h 


-- conjunction intro 

#check and.intro (and.left h) (and.right h)



-- having B and ¬ B
variable b : B
#check (and.right h) b



-- proof of commutativity of conjunction (∧) 
variable h : A ∧ B 
#check and.intro (and.right h) (and.left h)


-- unfortunately it remembers variable h from line 25. The declarations are not local. How to fix this? 
--easy solution: use a new variable name
variable h' : A ∧ B 
#check and.intro (and.right h') (and.left h')



-- The elim rule for implication: if p₁ is a proof of A → B and p₂ is a proof of A then p₁ p₂ is a proof of B. 

#check A → B → C   -- we get an error unknown identifier 'C'

variable C : Prop -- not that the line above still has an error 

#check A → B → C -- this is NOT  A → B and B → C 

-- adding some hypotheses 
variable p : A → B → C 
variable q : Q 
variable u : Q → A 

#check p (u q) 
#check (p (u q)) b



-- the implication intro rule is a bit more tricky 
-- in below we prove P → P ∧ P 
#check (assume p : P, and.intro p p )

-- in below we prove P → ¬¬ P 
-- what on earth is λ? 
#check (assume h: P, (u : ¬ P), (u h)  )

-- for now let us just use "assume" 
#check (assume h: P, assume u : ¬P, u h )



-- Above, we proved B ∧ A from the premise A ∧ B. We can instead obtain a proof of A ∧ B → B ∧ A as follows:
#check (assume h : A ∧ B, and.intro (and.right h) (and.left h))

-- note that A ∧ B → B ∧ A is a tautology, and it uses no premises.




-- Let us introduce a new Lean command, "example". This command tells Lean that you are about to prove a theorem. It should then be followed by the proof or expression itself.

-- When given this command, Lean checks the expression after the := and makes sure it has the right type. If so, it accepts the expression as a valid proof. If not, it raises an error.

example : A ∧ B → B ∧ A :=
assume h : A ∧ ¬ B,
and.intro (and.right h) (and.left h) -- our first trial did not work -- what is the error? 

example : A ∧ B → B ∧ A :=
assume h : A ∧ B,
and.intro (and.right h) (and.left h)



-- the expression “show A, from P” means the same thing as P alone, but it signals the intention that P is a proof of A. When Lean checks this expression, it confirms that P really is a proof of A, before parsing the expression surrounding it.

variables A B : Prop

example : A ∧ B → B ∧ A :=
assume h : A ∧ B,
show B ∧ A, from and.intro (and.right h) (and.left h)


example : A ∧ B → B ∧ A :=
assume h : A ∧ B, 
show B ∧ A, from and.intro
(show B, from and.right h) 
(show A, from and.left h)

-- "show" command makes the proofs easier for us humans to read. 
-- it also makes the proofs easier to write: if you make a mistake in a proof, it is easier for Lean to figure out where you went wrong and provide a meaningful error message if you make your intentions clear.


-- underscore
example : A ∧ B → B ∧ A :=
assume h, and.intro (and.right h) _



-- here is a lean proof of an example from week 2 lecture 1.  
example : ( ( P ∨ Q ) → R ) ↔ (P → R) ∧ (Q → R) := 
begin 
sorry 
end   
 









