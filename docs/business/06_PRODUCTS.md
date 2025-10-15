# 6) Products (what ships in MVP)

**Short version:** three simple products + a few shared rails. You can use each one on its own, and they click together when you’re ready.

---

## 1) ABDUCTIO — pre-commit judgment you can trust (ships now)

**What it does (in plain language):**  
Turns any claim into a **pre-commit promise score**: *(Credence, Confidence)* plus a one-page rationale you can read and share.

- **Credence** = how likely the claim is true *for you*.  
- **Confidence** = how sure we are about that estimate given the evidence we checked.

**What you get:**  
- A short, auditable breakdown of the claim into smaller claims (method, fit, adherence, measurement).  
- Two numbers (Credence, Confidence) and a clear **“stop here”** recommendation matched to the stakes.  
- A neat **PDF/JSON export** you can attach to emails, proposals, and applications.

**Works standalone:** use ABDUCTIO to decide *without* any SPONSIO settlement attached.

**Day-one example:**  
> “Two sessions of this sleep program will reduce my ISI score by ≥6 points.”  
> ABDUCTIO returns *(Credence 0.62, Confidence 0.70)* with a one-page explanation. You now have a *justified* yes/no—or a reason to investigate one step further.

**Bonus (launch wedge):** a guided **viability report** (DE) that packages your ABDUCTIO into an accepted dossier reviewers can sign.

---

## 2) SPONSIO Earnest — outcomes settle money (ships now, no custody)

**What it does:**  
Lets two parties **pre-register a simple test** and move money by that rule—**authorize now; capture or refund automatically** when the outcome is measured.

**What it looks like:**  
- You agree the pass/fail rule up front (plain language).  
- The client’s card is **authorized** (not captured).  
- After the check, the platform **captures the success fee** or **auto-refunds** per the rule.  
- A single-page **decision export** (PDF/JSON) shows what happened.

**Why it’s safe:** uses standard payment rails (authorize/capture/refund). We **never hold funds** or market “escrow.”

**Day-one templates:**  
- **Sleep coaching:** “If ISI ≤ 12 at week 4, capture success fee; else refund it.”  
- **Smoking cessation:** “Capture success fee only if 90 consecutive nicotine-free days are logged.”

**Edge cases (kept simple):**  
- **Adherence rule** avoids “no-show” games (e.g., ≥6/7 diary entries per week).  
- **Neutral review path** with a short SLA if something’s unclear.

---

## 3) SPONSIO Virtual — fuel pre-commit work without touching money (ships now)

**What it does:**  
Provides two non-monetary pieces that make the system sturdier from day one:

- **Merit (separate, not money):** a domain-specific **trust score** for raters/reviewers (how reliable your judgment has been). It **weights** voices and **sets** evidence/hold requirements; it is **not transferable** and **not a currency**.  
- **Report Passes / Vouchers:** **issuer-only** credits **redeemable only for ABDUCTIO outputs** (e.g., viability reports). No cash-out, no P2P. They fund pre-commit analysis and add light sybil friction.

**How you’ll actually use it:**  
- A founder buys **two Report Passes**, redeems one for a viability report, and keeps one for a second review later.  
- Reviewers and AI assessors **earn Merit** when their evaluations are adopted and hold up—so their voice counts more next time.

---

## Shared rails we ship in the MVP (the “dockyard”)

- **Domain registry (small, sane start):** `/coaching/sleep`, `/coaching/habit_control/smoking_cessation`, `/entrepreneurship/viability_report/de`, plus a few cross-domain standards (identity level, evidence export, payment timing).  
- **Verification instruments:** ready-to-use **sleep diary & ISI** forms; simple nicotine check-ins; witness attestations.  
- **Decision exports:** identical, one-page **PDF/JSON** for any decision (kept/not kept; what rule fired; timestamps).  
- **Identity levels:** basic sign-in for browsing; upgraded checks for higher-stakes actions.  
- **Dispute micro-flow:** a lightweight, time-boxed review path (most decisions will auto-resolve).

---

## Day-one user journeys (so you can picture it)

**Client (sleep):**  
1) Runs **ABDUCTIO** on a sleep promise → sees *(Credence, Confidence)*.  
2) Books with **Earnest** terms → card authorized, rule pre-registered.  
3) Logs a 7-day diary → outcome measured → success fee captured or refunded, export saved.

**Coach:**  
1) Picks a ready **Earnest** template → customizes thresholds within allowed ranges.  
2) Shares a booking link with “authorize now; capture on kept.”  
3) Gets fewer disputes, better close rates, and a real **domain reputation**.

**Founder (DE viability):**  
1) Buys **Report Passes** (Virtual) → redeems for an **ABDUCTIO** viability report.  
2) Reviewer signs the dossier → you submit a clean, accepted package.

---

## What we are *not* shipping in the MVP (on purpose)

- **Sponsio Core / v1.0.0** (true staking/slashing with a monetary stake unit).  
- Any form of **funds custody** or “escrow/wallet” UX.  
- **Transferable** or **cash-redeemable** credits.  
- A big, open marketplace. (We begin with **two coaching domains** + one **reviewer lane** and do them well.)

---

## What “good” looks like in the MVP

- **ABDUCTIO:** your one-page score and rationale are clear enough that a first-time reader can decide without calling a friend.  
- **Earnest:** decisions auto-resolve; disputes are rare; money moves exactly when the rule says.  
- **Virtual:** Report Passes get ABDUCTIO work done where it matters; Merit starts to separate strong evaluators from noise.

**Bottom line:** decide with **justified confidence** (ABDUCTIO).  
Pay on **verified outcomes** (Earnest).  
Bootstrap pre-commit work and rater quality **safely** (Virtual).  
All three ship now—and each is useful on its own.
