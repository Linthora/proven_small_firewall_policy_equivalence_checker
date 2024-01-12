# Firewall Policy Equivalence Checker

## Overview

This project serves as an exploration of fundamental proof assistants, their significance, and their application in software development. The primary objective is to grasp the benefits of utilizing proof assistants through a concrete example—building a Firewall Policy Equivalence Checker. The entire process involves formalizing the checker, proving its properties within the Isabelle/HOL proof assistant, and implementing it in a small Scala test environment.

## Learning Objectives
1. **Understanding Proof Assistants:**
   - Delve into the fundamentals of proof assistants and their role in ensuring correctness and reliability in software development.

2. **Concrete Example: Firewall Policy Equivalence Checker**
   - **Formalization:**
     - Explore the complexities of security policy equivalence within firewalls.
     - Define rules for filtering packets based on source IP addresses using Isabelle/HOL.
     - Develop the `filter` function to determine address acceptance within security policies.

   - **Properties and Proofs:**
     - Create a function (`equal`) to decide the equivalence of two security policies.
     - Formally prove properties of the `equal` function with respect to the `filter` function.

   - **Implementation in Scala:**
     - Generate Scala code for the proven `equal` function.
     - Integrate the Scala code into a small test environment
     - Conduct extensive testing using Scala's testing capabilities (not really for testing per say, but to convince us of the mighty power of proof assistant <3)

## Project Structure
- **Isabelle/HOL Definitions, Proofs and Properties:**
  - Definitions, methods and proofs of our own Set in `tp2.thy`
  - Security policy definitions, methods and proofs (and intermediate lemmas) and the `filter` function in `tp5.thy`.

- **Scala Implementation:**
  - Review the Scala project structure and code in `tp5.scala`.
  - Understand how the formally proven `equal` function is integrated into a Scala environment.

## Acknowledgment

Special thanks to our dedicated professor and practical work trainer, for guiding us through the intricacies of proof assistants and providing valuable insights throughout the project.
