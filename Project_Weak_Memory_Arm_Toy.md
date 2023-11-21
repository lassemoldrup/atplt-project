### 1. An ARM-like toy model
We consider a simplified, ARM-reminiscing memory model, called ARM-TOY where an auxiliary *dependency-ordered-by (dob)* relation captures, in each thread-local execution, the pairwise orderings of all events of the same thread.

Let's assume that programs only perform load and store operations (no fences, no RMWs).

We use $S;R$ to represent the composition of two relations $S$ and $R$.
We use $S^{-1}$ to denote the inverse of relation $S$.
We use $S^{?}$ to denote the reflexive closure of relation $S$.
For a set $X$, we use $[X]$ to refer to the identiy relation.

Recall that $fr=rf^{-1};mo$, $rfe=rf\setminus po$, $moe=mo\setminus po$, $fre=fr\setminus po$.
The coherence (per location) axioms are:

* **Write coherence (per location):** $(mo_x\cup po_x)$ is acyclic
* **Read coherence (per location):**  $rf_x^{-1};mo_x;rf_x^{?};po_x$

These two can be written as one axiom:
* **SC-per-location:** $po_x\cup rf_x \cup mo_x \cup fr_x$ is acyclic.

The $dob$ relation finds its way into an *External Coherence* axiom:

* **External Coherence:** $(dob \cup rfe \cup moe \cup fre)$ is acyclic.

An execution (graph) is a tuple $G=(E,po,rf, mo, dob)$. This is close to what we have seen in our lectures, but we have inserted $dob$ as the extra component.
$G$ is *consistent* in ARM-TOY model if it satisfies per-location coherence and external coherence.

In practice, when we just observe the execution of a program, we don't typically have access to the $mo$ and/or $rf$ relations. 
Instead, we talk about *abstract executions* (sometimes also called *candidate executions*) that have the form
1. $H=(E,po,rf, dob)$ (note, $mo$ is missing), or even
2. $H=(E,po, dob)$ (note, both $mo$ and $rf$ are missing).

The *consistency checking* problem for abstract executions of type 1. amounts to deciding whether there is an $mo$ such that the execution $G=(E,po,rf, mo, dob)$ is consistent in ARM-TOY.
Similarly, for abstract executions of type 2., we need to figure out whether there are $rf$ and $mo$ such that, again, $G=(E,po,rf, mo, dob)$ is consistent.

Both problems are typically NP-complete across models, but the first one is in polynomial-time for some models.


### 2. Computational questions
How do we decide consistency? We can enumerate all possible $mo$'s and $rf$'s and test whether all axioms are satisfied for each istance.
From a computational perspective, this is way too naive and slow, we'd like to do better.
Let's focus on abstract executions of type 1. above from now on, so the goal is to infer the $mo$ order.
*Saturation* is a polynomial-time technique for infering some forced $mo$ edges, by following the axioms of a given model.
Saturation is *complete*: if an abstract execution is consistent, saturation will never return "inconsistent".
It has been used in the past in the context of $SC$ and $RA$ (maybe also others) -- see references below. 

Goals:

1. *[Algo + Programming]* Develop your own saturation procedure for ARM-TOY. Use it to solve consistency, and compare it with the naive, fully enumerative approach.

2. *[Theory]* Is saturation for SC also sound when there is only one memory location written/read? Is it also sound when there are only two memory locations written/read.

3. *[Algo + Programming]* Specialize your saturation technique for the settings where $dob=\emptyset$ and $dob=po\setminus [Writes];[Reads]$, and repeat 1.

4. *[Theory, likely difficult]* Is consistency checking for abstract executions of the form $H=(E,po, dob)$ in polynomial time for bounded number of threads and memory locations?

Jean has some small infrastructure that you can use to obtain (abstract?) executions out of source code, that you can use as input to your tools.

### 3. Model questions / Use of a proof assistant

Here are some targets to be proven in a proof assistant (but first, check on paper -- I haven't thought hard about some of these).

Goals:

1. Prove that when $dob=\emptyset$, ARM-TOY coincides with C11's Relaxed fragment (i.e, only SC-per-location).
2. Prove that when $dob=po$, ARMO-TOY coincides with SC.
3. Prove that when $dob=po\setminus [Writes];[Reads]$, ARM-TOY coincides with TSO (this is likely straight from the slides).
4. Prove that saturation is complete (ie, if it deems an abstract execution inconsistent, it is truly inconsistent). You can do this for ARM-TOY, or even plain SC.


The proof targets here play nicely with the computational questions above. E.g., by proving 1. here and 2. above, you have that saturation is sound and complete for the Relaxed fragment of C11 (you can also try to prove 2. above in a proof assistant, not sure how challenging it will be).
By proving 3 here, you have that your saturation is also complete for TSO.

### 4. Suggested reading and class presentation

**Saturation**

https://dl.acm.org/doi/10.1145/3371085 

This paper develops saturation (called "closure" here) for predicting data races. You only need Section 3.1, up to figure 3.


https://dl.acm.org/doi/10.1145/3276505 

This paper describes an approach for model checking the Release-Acquire fragment of C11. You only need to read up to Section 4, and essentially understant the "Saturated Semantics". For Release-Acquire, saturation is both sound and complete, so consistency checking actually takes polynomial time. Skip the actual DPOR algorithm (Section 5).

One of you could present both papers in one of your talks (their relevant parts regarding saturation).


**The ARM model**

https://dl.acm.org/doi/10.1145/3158107 for a recent formal account of the ARM model.


**The full C11 model**

https://dl.acm.org/doi/10.1145/3062341.3062352

In class we talked independently about various fragments of C11 (SC/Release-Acquire/Relaxed), but what about programs that mix them?
The most recent model is (I believe) scattered around many references, but this is a good, recent attempt at its formalization.
It also mentions RMW instructions, that we skipped in the lectures.
