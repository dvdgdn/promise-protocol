# 12) Legal / Compliance Strategy

**Plain idea:** build for trust, not thrills. We ship what’s clearly allowed **today** (no custody, closed-loop vouchers, privacy by design), and we gate anything ambiguous. When in doubt, we pause the boat, fix one thing, and try again.

---

## What we are (and aren’t)

- **We are:**  
  - A **decision-support + payments-timing** platform (SPONSIO Earnest) using acquirer/PSP **authorize → capture/refund** flows.  
  - A **reasoning/export** service (ABDUCTIO) that produces **pre-commit scores** and clean **PDF/JSON/VC** dossiers.  
  - A **cooperative** stewarding an **open protocol** and closed-loop **Report Passes** for ABDUCTIO exports.  

- **We are not:**  
  - An **escrow**, **wallet**, **bank**, or **e-money** issuer.  
  - A **gambling** or **derivatives** venue.  
  - A **medical** provider or advertiser of “healing” claims.

**Copy guardrails (always):** say “**payment timing**” and “**authorize now; capture on kept**.” Never say “escrow,” “wallet,” “token,” “coin,” “guarantee,” or “insurance.”

---

## Four pillars (mapped to our products)

### 1) SPONSIO Earnest (money outcomes, no custody)
- **Payments:** Only via licensed PSPs (card/SEPA): **authorize → capture/refund** when the *pre-registered* rule fires.  
- **Windows:** If auth duration is too short, we **capture + auto-refund** the success component instead of holding.  
- **Disputes:** Time-boxed neutral review; simple artifacts (one-page decision export).  
- **Consumer rights:** Clear pricing; easy cancellation before work; standardized refunds when **NOT KEPT**.  
- **Marketing:** No medical/healing promises; we advertise **measurable improvements** and fair settlement.

**Legal gate (Earnest):**  
- No references to escrow/custody; PSP contract + ToS reviewed; help center article explains authorize/capture/refund.  
- If support tickets show confusion (>2%), pause and fix copy.

---

### 2) SPONSIO Virtual (closed-loop value; not money)
- **Instrument:** **Issuer-only Report Passes/Vouchers**, redeemable **only for ABDUCTIO exports**.  
- **Posture:** Closed loop; **no cash-out**, **no P2P transfer**, **no EUR peg**; narrow catalog (viability reviews + add-ons).  
- **Thresholds:** Internal **12-month counter** for total voucher volume; notify and/or narrow scope before limits.  
- **Labeling:** “Report Pass — redeemable only for ABDUCTIO exports; not money; non-transferable.”

**Legal gate (Virtual):**  
- Voucher T&Cs + counter live; <2% of tickets confuse vouchers with money. If breached, narrow catalog and relabel before resuming.

---

### 3) ABDUCTIO (reasoning + exports; special-category data hygiene)
- **Purpose:** Pre-commit judgment *(Credence, Confidence)* and **accepted dossiers** (e.g., viability exports).  
- **Roles:**  
  - For client-commissioned analyses: cooperative often acts as **processor** to providers/reviewers’ controller role; if we decide purposes jointly (e.g., shared scoring), we document **joint controllership**.  
- **Special data:** Sleep/health-adjacent inputs are **special category**—we obtain **explicit consent**, minimize fields, and separate identifiers.

**Legal gate (ABDUCTIO):**  
- DPA in place; explicit consent text for special data; DPIA completed before public launch; exports are reproducible and redactable.

---

### 4) Merit & Reputation (separate from money)
- **Merit is not currency.** Non-transferable, domain-scoped score used to weight evidence/stakes.  
- **Transparency:** Document how scores are computed; provide right to explanation at a human-readable level; support correction appeals.

**Legal gate (Merit):**  
- Publish scoring summary; maintain logs; allow challenge/appeal path; ensure LIAs (legitimate-interest assessments) are on file.

---

## Data protection (GDPR-first, privacy by design)

- **Lawful bases:**  
  - Earnest decisions & payments → **contract**.  
  - ABDUCTIO reputation & merit → **legitimate interests** with **balancing tests (LIA)**; where health-adjacent data is involved, add **explicit consent**.  
- **Minimization & separation:** Evidence in its own store; PII paths limited; hashes in the audit log; redaction keeps integrity (hash stays, PII goes).  
- **User rights:** Access/export (JSON/PDF), rectification, erasure (where compatible with accounting/audit).  
- **Sub-processors:** EU hosting; DPA + SCCs if outside the EEA; published list.  
- **Security:** Encryption at rest/in transit; role-based access; secrets vault; incident plan with **72-hour** breach notices.  
- **DSA basics:** Terms, notice-and-action, transparency page; we are not a VLOP and keep it simple.

**Privacy gate:**  
- DPIA completed; ROPA maintained; redaction workflow tested; breach runbook rehearsed.

---

## Consumer & content rules (plain-language guardrails)

- **Cooling-off / withdrawals:** Honor consumer withdrawal rights for distance contracts; if the user requests immediate performance of ABDUCTIO exports, obtain explicit acknowledgment that the right may lapse after full performance.  
- **Health-adjacent marketing:** Avoid “cure/treat” language; use “measurable improvement” and **coaching** framing with instruments (e.g., ISI, diaries).  
- **Clarity:** Every template has a **Plain Promise** line and a **Pass/Fail** line a non-specialist can read.

**Copy gate:**  
- Template reviews for claims; if a recipient flags a misleading claim, freeze that template version and patch.

---

## Taxes & invoices

- **VAT:** Platform fees and ABDUCTIO exports invoiced with VAT as applicable; vouchers recognized as **deferred revenue** and recognized on redemption.  
- **Receipts:** Decision export attaches to the receipt for Earnest captures/refunds; clean trail for chargebacks and audits.

---

## Governance & record-keeping

- **Co-op statutes:** member primacy; reserved matters; investing-member limits.  
- **Logs:** Append-only event log with content hashes for evidence and decisions.  
- **Audits:** Quarterly compliance checks; annual financial audit; public metrics page.

---

## Red flags & automatic kill switches

| Red flag | Immediate action |
|---|---|
| Any team holds client funds | **Stop** the flow; route via PSP only; audit copy & code |
| Vouchers marketed broadly or redeemable outside ABDUCTIO | Narrow catalog; pull copy; relabel; consider notification |
| Health/medical claims creep | Pull page; replace with measurable-improvement framing |
| Disputes > 5% two weeks | Pause intake; tighten template (median windows, adherence) |
| Users confuse vouchers with money > 2% tickets | Freeze voucher sales; relabel; add explainer; resume after <2% |
| Evidence includes unnecessary PII | Patch forms; purge; re-train team |

---

## Roles & paperwork (what’s on file)

- **ToS** (no custody; payment timing; consumer terms).  
- **Privacy Notice** (Art. 13/14), **DPIA**, **ROPA**, **LIA**(s).  
- **DPAs** with PSP, hosting, analytics; **SCCs** if needed.  
- **Voucher T&Cs** (issuer-only, non-transferable, no cash-out).  
- **Partner MoUs** (reviewers/coaches), **Data Sharing/Joint Controller** addenda if applicable.  
- **Reviewer sealing** policy (VC issuance, signatures, revocation).

---

## Words we use (and don’t)

- **Use:** “decision export,” “payment timing,” “authorize/capture/refund,” “issuer-only Report Pass,” “measurable improvement,” “coaching,” “pre-commit score.”  
- **Avoid:** “escrow,” “wallet,” “token/coin,” “guarantee/insurance,” “cure/treat,” “bank-like.”

---

## Future path (what waits behind a legal gate)

- **Sponsio Core (true staking/slashing):** only with a licensed **EMI/PI** or structured program where the monetary unit is compliant (expect full safeguarding, capital, audits).  
- **Event-contingent payouts/markets:** only with specialist counsel; many jurisdictions treat these as **gambling/derivatives**. Not in MVP.  
- **Broader voucher networks:** only if/when we can keep a valid **limited-network** posture with notifications.

---

## The compliance promise (how we keep ourselves honest)

- **Public gates:** We publish the legal/tech/market/economic gates and won’t scale a boat that hasn’t cleared them **two months running**.  
- **Small artifacts:** Every outcome and export has a one-page summary that a skeptic can read.  
- **Pause power:** If any gate turns red, we pause new intake for that boat. No exceptions.

**Bottom line:** We win by being boring where the law wants boring—no custody, no pseudo-money, no magical claims—and by being crystal clear where people want clarity: *what was promised, what was measured, and what happened.*
