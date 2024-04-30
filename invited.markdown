---
layout: page
title: Invited Talks
permalink: /invited/
---

### **Title**: Coinductive Reasoning in [Isabelle/HOL](https://isabelle.in.tum.de)

**Speaker**: [Prof. Dmitriy Traytel](https://traytel.bitbucket.io) from the University of Copenhagen

**Abstract**: Coinductive methods are used to reason about the infinitary behavior of systems, e.g., manifested in traces of useful (potentially) non-terminating programs. Examples of such programs range from semi-decision procedures for automated theorem proving to web servers interacting with clients. In this presentation, I will survey the coinductive capabilities of the Isabelle proof assistant, with a focus on defining and reasoning about corecursive functions. In particular, I will highlight challenges for proof automation that arise in this setting.

<a href="https://traytel.bitbucket.io" target="_blank">
<img src="https://raw.githubusercontent.com/WAIT2024/WAIT2024.github.io/main/image/dmitriy_traytel.png" height="200">
</a>

### **Title**: Gauging the strength of inductive theorem provers

**Speaker**: [Dr. Stefan Hetzl](https://dmg.tuwien.ac.at/hetzl/) from the Vienna University of Technology

**Abstract**:

Due to Gödel's incompleteness theorems, methods for inductive theorem proving
are inherently incomplete. Nevertheless, for improving our understanding of a
particular method `M` it is useful to characterise the set of theorems provable
by `M` (given unlimited time and memory).

Standard notions and techniques from mathematical logic provide an adequate
basis for carrying out such analyses and for building on them to obtain
additional results about `M`. More concretely, we try to find a theory `T` that is
closely related to `M` in the sense that `T` proves exactly the same theorems as `M`
or, more realistically, every theorem provable by `M` is provable by `T` (but `T`
does not prove "much more").

In either case, model-theoretic techniques can then be used to obtain a
practically relevant independence result, i.e., a simple and natural true
statement unprovable in `T`, and hence unprovable in `M`. Such statements are
suitable challenge problems for the improvement of inductive theorem provers.

In this talk I will present the analyses of several popular methods and put
particular emphasis on the challenge problems obtained from them. This talk is
based on joint work with [Jannik Vierling](https://jvierling.github.io).

<a href="https://dmg.tuwien.ac.at/hetzl/" target="_blank">
<img src="https://raw.githubusercontent.com/WAIT2024/WAIT2024.github.io/main/image/stefan_hetzl.jpeg" height="200">
</a>

### **Title**: Induction in Saturation-Based Proving

**Speaker**: [Prof. Andrei Voronkov](http://voronkov.com) from the University of Manchester and [Ms. Petra Hozzová](https://logic-cs.at/phd/students/petra-hozzova/) from the Vienna University of Technology

**Abstract**:

Induction in saturation-based first-order theorem proving is a new exciting direction in automated reasoning, bringing together inductive reasoning and reasoning with full first-order logic extended with theories.

In this tutorial, we dive into our recent results in this area.

Traditional approaches to inductive theorem proving, based on goal-subgoal reduction, incompatible with saturation algorithms where the search space can simultaneously contain hundreds of thousands of formulas, with no clear notion of a goal.

Rather, our approach applies induction by theory lemma generation: from time to time we add to the search space instances of induction axioms, which are valid in the underlying theory but not valid in first-order predicate logic. To formalise this, we introduce new inference rules adding (clausal forms of) such induction axioms within saturation. Applications of these rules are triggered by recognition of formulas in the search space that can be considered as goals solvable by induction.

We also propose additional reasoning methods for strengthening inductive reasoning, as well as for handling recursive function definitions. We implemented our work in [the Vampire theorem prover](https://vprover.github.io) and demonstrate the practical impact in experiments.

The tutorial will consist of the following parts supported by live demonstrations:

1. Introduction to saturation-based reasoning and superposition
2. Integration of induction into saturation [1]
3. Case studies: integer induction and recursive definitions [2, 3]
4. How far can we go with induction in saturation?
5. Future outlooks: using automated inductive proving in proof assistants and beyond

**References**:
- [1] [Induction in Saturation-Based Proof Search (2019)](https://doi.org/10.1007/978-3-030-29436-6_28), G. Reger and A. Voronkov, in Proc. of CADE 
- [2] [Integer Induction in Saturation (2021)](https://doi.org/10.1007/978-3-030-79876-5_21), P. Hozzová, L. Kovács, and A. Voronkov, in Proc. of CADE 
- [3] [Induction with Recursive Definitions in Superposition (2021)](https://doi.org/10.34727/2021/isbn.978-3-85448-046-4_34), M. Hajdu, P. Hozzová, L. Kovács, and A. Voronkov, in Proc. of FMCAD 
- For a survey , also see: [Getting Saturated with Induction (2022)](https://doi.org/10.1007/978-3-031-22337-2_15), M. Hajdu, P. Hozzová, L. Kovács, G. Reger, and A. Voronkov, in Principles of Systems Design

<div style="display: flex; align-items: center;">
  <a href="http://voronkov.com" target="_blank">
    <img src="https://raw.githubusercontent.com/WAIT2024/WAIT2024.github.io/main/image/andrei_voronkov.jpg" height="200" style="margin-right: 20px;"> <!-- Adjust margin as needed -->
  </a>
  <a href="https://logic-cs.at/phd/students/petra-hozzova/" target="_blank">
    <img src="https://raw.githubusercontent.com/WAIT2024/WAIT2024.github.io/main/image/petra_hozzova.jpg" height="200">
  </a>
</div>
