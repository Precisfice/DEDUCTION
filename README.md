# DEDUCTION
Dose Escalation Designs in Universal Context of Titration for Oncology Drug Development

## Introduction

> The category-theoretic perspective can function as a simplifying
> abstraction, isolating propositions that hold for formal reasons
> from those whose proofs require techniques particular to a given
> mathematical discipline.
>
> — Riehl, Preface to 'Category Theory in Context' (2016)

This project aims to formulate dose-escalation trial protocols using
ideas from Applied Category Theory (ACT), carrying out the attendant
computations on a 'workbench' developed using the monotonic subset of
Prolog, including CLP(ℤ).  In accordance with the quotation above,
this categorial formulation serves to exhibit certain properties of
dose-escalation designs as deducible from more basic premises than we
may otherwise appreciate.  Working in Prolog promotes a clarification
of thought and elegance of expression that harmonize perfectly with
the intellectual spirit of categorial investigations such as these.
(For an extensive discussion of the advantages of Prolog in medical
and other such safety-critical applications, and our rationale for
selecting [Scryer Prolog](https://www.scryer.pl/) in particular,
please see Section 2 of [1].)

## Background

DEDUCTION represents the latest—and possibly conclusive—development
within the Dose Titration Algorithm Tuning (DTAT) research programme,
which has been ongoing now for the better part of a decade.  The full
bibliography found [here](https://precisionmethods.guru/bibliography)
links to 'lay explainers', short videos or online apps accompanying
most of the scholarly outputs, reflecting the DTAT programme's long
commitment to lay outreach.  Although this outreach has been pursued
with cancer patient advocates most especially in mind, these resources
may prove useful even to experts in adjacent fields, since DTAT draws
upon ideas from several disciplines not often brought under one roof.

## Process

We are carrying out the DEDUCTION effort in this public repository.
Presently, the core output is an evolving monograph `catform.pdf`,
built from `catform.tex` and subject to occasional tagged releases.
Our Prolog workbench is being developed mainly in `catform.pl`, using
Markus Triska's [ediprolog](https://www.metalevel.at/ediprolog/).

## Progress

DEDUCTION is presently (as of Christmas Day, 2024) on the cusp of
solving — within weeks, not months — two crucial problems in
dose-escalation protocol design:

* Starting with a *given* dose-escalation design, possibly defined in
  terms depending on enrollment of non-singular cohorts to be dosed
  simultaneously, extend this design faithfully to achieve what has
  been termed *rolling enrollment* [2] while accounting for the
  possibility of pending toxicity assessments [3].

* Given any dose-*escalation* design, in which *by definition*
  "intra-patient dose escalation is not allowed" [4], extend this
  faithfully to a dose-*titration* design that dispenses with this
  constraint.

## References

1. Norris DC, Triska M. An Executable Specification of Oncology
   Dose-Escalation Protocols with Prolog. February 13, 2024.
   http://arxiv.org/abs/2402.08334

2. Skolnik JM, Barrett JS, Jayaraman B, Patel D, Adamson
   PC. Shortening the Timeline of Pediatric Phase I Trials:
   The Rolling Six Design. *Journal of Clinical Oncology*.
   2008;26(2):190-195.
   [doi:10.1200/JCO.2007.12.7712](https://ascopubs.org/doi/abs/10.1200/JCO.2007.12.7712)

3. Frankel PH, Chung V, Tuscano J, et al. Model of a Queuing Approach
   for Patient Accrual in Phase 1 Oncology Studies. *JAMA Network Open*.
   2020;3(5):e204787-e204787. [doi:10.1001/jamanetworkopen.2020.4787](https://jamanetwork.com/journals/jamanetworkopen/fullarticle/2765855)

4. Norris DC. Ethical Review and Methodologic Innovation in Phase 1
   Cancer Trials. *JAMA Pediatrics*. 2019;173(6):609.
   [doi:10.1001/jamapediatrics.2019.0811](https://jamanetwork.com/journals/jamapediatrics/article-abstract/2731126)

