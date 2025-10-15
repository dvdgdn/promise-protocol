# 2) Solution Overview — The Promise Stack

## The Stack at a Glance
We separate *how you decide* from *how you settle*—and we make both measurable.

- **ABDUCTIO (pre-commit):** Turns any claim into a **pre-commit promise score** = *(Credence, Confidence)* plus a one-page rationale and a stopping rule (“enough evidence for these stakes”). Works **standalone**.
- **SPONSIO (post-commit):** Moves value only when a **pre-agreed outcome** is verified. Two safe rails now, one advanced later:
  - **Sponsio Earnest (today):** payment authorizations → **capture or refund** based on the result (no custody).
  - **Sponsio Virtual (today):** **issuer-only Report Passes/Vouchers** redeemable for ABDUCTIO outputs (closed loop; not money) + light **sybil friction**.
  - **Sponsio Core (later):** true staking/slashing with **Sponsio Credit** when legally ready.
- **Merit (separate, not money):** A non-transferable **trust score** that weights voices and sets evidence/hold requirements. Kept separate to preserve integrity and avoid regulatory creep.
- **Promise Foundation (co-op):** The steward. Open protocol, member ownership, **patronage** (surplus sharing) + **merit** incentives.

---

## What Each Part Does

### 1) ABDUCTIO — Make a justified decision *before* you commit
- **Input:** “This program will improve my sleep by ≥6 ISI points,” “This business will be viable,” “This hire will succeed.”
- **Process:** Decompose the claim → check evidence on the smaller claims → aggregate into two numbers:
  - **Credence:** probability the claim is true for *you*.
  - **Confidence:** how stable that probability is given the evidence you have.
- **Output:** *(Credence, Confidence)*, a short explanation you can read, and a “stop here” recommendation matched to the stakes.
- **Use it alone:** You can run ABDUCTIO for any decision—no SPONSIO required.
- **Licensing:** Free/MIT core so contributors can extend it.

### 2) SPONSIO — Settle on outcomes, not opinions
- **Agree the test up front:** “If ISI ≤ 12 at week 4, capture the success fee; else refund it.”  
- **Measure automatically:** log diaries, scores, or simple checks you select.  
- **Settle automatically:** value moves per the rule; a PDF/JSON audit is saved.

**Two safe rails today**
- **Sponsio Earnest:** Use standard payment APIs (authorize → capture/refund). No wallets, no custody, no escrow license. Great for coaches and services that want “pay on result.”
- **Sponsio Virtual:** Give or sell **Report Passes/Vouchers** that can be redeemed **only** for ABDUCTIO outputs (e.g., viability reports). Close the loop, fund reviews, add sybil friction—without touching e-money.

**Later**
- **Sponsio Core:** When partnered/licensed, enable true stake/slash (**Sponsio Credit**) for high-stakes promises and assessments. ABDUCTIO and Merit plug in unchanged.

### 3) Merit — Keep judgment clean
- **What it is:** Domain-aware **reliability score** (not currency).  
- **What it does:** Influences who needs stronger evidence, how big a hold is, or whose evaluation counts more.  
- **What it isn’t:** Money, points you can trade, or anything you can buy.

### 4) The Foundation — Open protocol, member upside
- **Protocol:** Executable rules for promises, evidence, and settlement (no gatekeepers—pass the specs).  
- **Co-op incentives:** Members share surplus (**patronage**) and earn **merit**—so they’re financially and reputationally motivated to add templates, verify outcomes, and invite peers.

---

## How It Fits Together (use together or separately)
1. **Decide with ABDUCTIO:** You get *(Credence, Confidence)* and a plain-English rationale.  
2. **(Optional) Settle with SPONSIO:** If there’s a provider and a price, register a simple pass/fail rule.
3. **Close the loop:** Outcomes feed back to improve future ABDUCTIO estimates. Merit updates who needs how much proof next time.

> **Key point:** ABDUCTIO and SPONSIO are complementary but independent. You can adopt either one first.

---

## What Ships Now vs Later
- **Now (MVP):** ABDUCTIO Free (pre-commit scores + exports), Sponsio Earnest (authorize/capture/refund), Sponsio Virtual (Report Passes/Vouchers + Merit).  
- **Later:** Sponsio Core (licensed staking/slashing), deeper integrations, and more verification instruments.

**Bottom line:** Decide with *justified confidence* (ABDUCTIO). Pay on *verified outcomes* (SPONSIO). Grow a system that rewards people who actually keep their promises (Merit + co-op).
