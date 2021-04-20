On the idea that the “least reflexive relation” definition of equality begs the question: I noticed that if you try to formalise this definition using Knaster-Tarski, then you end up needing equality to express it. If you write:

----------
(x,x) ∈ eq

Then the associated monotone function will be:

F(S) := {(x,x) | x ∈ A}

But formally, to define a set using comprehension, we need to use the schema {q ∈ Q | P(q)} where Q is some set and p is a predicate.
In this case, we want to take Q = A*A and P((x,y)) = (x == y).

I don't know what conclusion to draw from that, but I found it kind of interesting that if you unfold the definitions enough, then in set theory this definition ends up relying on the built-in notion of equality. So you don't seem to be able to use this method to define equality from nothing, at least in set theory.