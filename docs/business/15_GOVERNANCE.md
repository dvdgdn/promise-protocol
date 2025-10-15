# 15) Governance & Incentives

**Short version:** member-owned, spec-driven, and incentive-aligned. One-member-one-vote for the big stuff; **merit** (not money) weights domain decisions; **patronage** shares surplus by use. Boats run autonomously, but gates and transparency keep the system honest.

---

## What “member-owned” means here
- **Legal form:** a multi-stakeholder cooperative (eG).  
- **Member classes:**  
  1) **Providers** (coaches, service firms)  
  2) **Reviewers** (analysts/certifiers)  
  3) **Workers** (builders/ops)  
  4) **Beneficiaries** (end users/clients)  
  5) **Investing Members** (bounded, non-controlling capital)
- **Join:** apply, buy a share, accept the statutes & code of conduct. You can contribute without joining; membership adds **patronage** and **voting** rights.

---

## Three decision layers (clear lanes, zero confusion)
1) **Core Protocol (Reserved Matters)**  
   - What: payment timing rules, evidence/export integrity, identity levels, governance rules.  
   - How: **concurrent majorities** — a majority of *all* members **and** a majority in each member class. One-member-one-vote.  
   - Change cadence: rare, after RFC + GA debate.

2) **Domain Standards (Per-class Majority + Merit weighting)**  
   - What: the standards inside a namespace (e.g., `/coaching/sleep`) and their parameters.  
   - Who votes: **the class that uses them** (Providers vote on provider standards; Reviewers on evidence standards).  
   - How: one-member-one-vote **plus** **Merit weighting** within the domain:  
     ```
     VoteWeight = 1.0 + log10(YourDomainMerit / MedianDomainMerit)
     (capped at 3.0×)
     ```
     Merit is *non-monetary* and *non-transferable*. It rewards good judgment, not spend.

3) **Experiments (Permissionless)**  
   - What: new templates/tools that **pass core specs**.  
   - How: no vote to ship; adoption decides. If ≥3 independent users adopt with good outcomes, it can be proposed as a Standard.

---

## Merit (the measurement layer, not money)
- **What it is:** a domain-scoped score for **calibration** and **discrimination** (how often you were right; how well your work holds up).  
- **How you earn it:**  
  - Your template is adopted and yields **KEPT** outcomes.  
  - Your review/export is used and **accepted**.  
  - Your tool/spec is adopted and stays reliable.  
- **Formula (intuitive):**  
  `Merit = Adoptions × QualityScore × TimeDecay` with a ~6-month half-life.  
- **What it does:**  
  - Weights your vote in **Domain Standards** (capped).  
  - **Modulates stakes & evidence**: higher-merit providers need smaller holds and lighter evidence; low-merit need stronger proof.  
  - Prioritizes **bounty invites** and review queues.  
- **What it’s not:** currency. It cannot be sold, transferred, or redeemed.

---

## Patronage (the money that comes back)
At year-end, surplus (after reserves and capped share dividends) is shared by **usage**:

| Pool share (illustrative) | Basis |
|---|---|
| **Providers ~50%** | Net GMV from **KEPT** outcomes (Sponsio) |
| **Reviewers ~20%** | Verified ABDUCTIO exports used in dossiers |
| **Workers ~25%** | Wage share / hours contributed |
| **Beneficiaries ~5%** | Engagement & verified outcomes participated |

- Transparent formula; board proposes, GA approves.  
- Paid in cash or member credits; fully auditable.

---

## Bounties & recognition
- **Spec bounties:** posted from the Product & Risk Fund (e.g., evidence templates, domain standards).  
- **Priority routing:** top-merit contributors in the domain get first notification.  
- **Leaderboards:** public, domain-scoped; show recent contributions (with decay).  
- **Attribution chains:** derivative specs share a slice of merit upstream.

---

## Anti-capture & anti-gaming
- **Merit caps** in voting (max 3×).  
- **Time decay** prevents “forever power.”  
- **No self-dealing merit:** your own use of your spec doesn’t count; **≥3 independent adopters** required.  
- **Wilson bounds & recency** in DomainScore to curb cherry-picking.  
- **Open logs:** merit events and adoption counts are public; challenge process exists.  
- **Concurrent majorities** block class capture on core matters.

---

## Fleet governance (how boats stay autonomous *and* accountable)
- **Boats own their P&L and roadmap** (e.g., ABDUCTIO—Viability, Earnest—Sleep).  
- **Transfer pricing:** boats “buy” shared rails (identity, payments, exports) at posted internal prices; no hallway politics.  
- **WIP limits:** max two boats in build/scale at once.  
- **Gate board:** each boat must be green on **technical, legal, market, economics** for two consecutive months to scale. Any red → **pause intake** until fixed.

---

## Investor Charter (if capital participates)
- **No control, no board seats by right.**  
- **Returns capped** (e.g., preferred return + cap, or revenue-share with sunset).  
- **Member primacy** enshrined; reserved matters cannot be altered by investment terms.  
- **Transparency:** investor updates published alongside member metrics.

---

## Transparency kit (what we publish)
- **Metrics page:** kept-rate, acceptance %, auto-decision %, disputes %, contribution margin per boat.  
- **Governance page:** upcoming votes, proposer rationale, results.  
- **Specs repo:** all standards & templates (versioned), test suites, change logs.  
- **Quarterly merit report:** distributions, top contributors, challenges resolved.

---

## Member responsibilities (simple and enforceable)
- **Follow the templates:** don’t change rules mid-promise.  
- **Respect privacy:** use only required evidence; redact on request.  
- **No misleading claims:** plain-language promises only.  
- **Conflict disclosures:** reviewers reveal financial ties; abstain where needed.  
- **Code of conduct:** respectful collaboration; zero tolerance for harassment or fraud.

Enforcement: warning → suspension → expulsion (GA oversight; appeal path).

---

## How a newcomer levels up (a concrete path)
1) **Start as a contributor:** submit a template or run ABDUCTIO for clients; earn first **Merit**.  
2) **Join the co-op:** get **patronage** and voting rights.  
3) **Become a domain voice:** your Merit weights standards votes and gets you first look at bounties.  
4) **Launch a boat:** propose a value line, pass specs, clear gates, and run with your own P&L.

---

**Bottom line:** governance here isn’t theater. It’s a **spec-first constitution** with payoffs for people who actually create value: **patronage** for the money, **merit** for the voice, and **gates** for the sanity. That’s how we keep the promises we make about keeping promises.
