import numpy as np
import matplotlib.pyplot as plt
from dataclasses import dataclass, field
from typing import Dict, List, Tuple, Optional, Union
import random
from collections import defaultdict
import pandas as pd
from scipy.stats import lognorm
import math

from . import params

@dataclass
class Promise:
    """Represents a promise made by an agent"""
    promiser_id: int
    domain: str
    stake: float
    value: float  # External value of the promise
    actual_outcome: Optional[bool] = None
    assessments: List[Tuple[int, bool]] = field(default_factory=list)  # (assessor_id, assessment)
    round_num: Optional[int] = None # Add round_num to Promise dataclass
    
@dataclass
class Agent:
    """Represents an agent in the protocol"""
    id: int
    credits: float
    merit: Dict[str, float] = field(default_factory=dict)
    honesty_rate: float = 0.9  # Probability of acting honestly
    coalition_member: bool = False
    external_payoff_mult: float = 1.0 # External benefit multiplier
    last_outcome: Optional[bool] = None # True if last promise kept, False if broken
    
    def get_merit(self, domain: str) -> float:
        return self.merit.get(domain, 0.0)
    
    def update_merit(self, domain: str, delta: float):
        current = self.get_merit(domain)
        # Merit bounded between 0 and 1
        self.merit[domain] = max(0.0, min(1.0, current + delta))

class AgencyProtocolSimulation:
    def __init__(self, 
                 n_agents: int = 100,
                 n_domains: int = 5,
                 alpha: float = 1.0,  # Credit weight in utility
                 beta: float = 2.0,   # Merit weight in utility
                 seed: Optional[int] = None):
        
        # Set random seed for reproducibility
        if seed is not None:
            np.random.seed(seed)
            random.seed(seed)

        self.n_agents = n_agents
        self.n_domains = n_domains
        self.domains = [f"domain_{i}" for i in range(n_domains)]
        
        # Economic parameters from params.py
        self.base_stake = params.BASE_STAKE
        self.alpha = alpha
        self.beta = beta
        self.gamma = params.GAMMA
        self.lambda_penalty = params.LAMBDA_PENALTY
        self.detection_sensitivity = params.DETECTION_SENSITIVITY
        self.discount_factor = params.DISCOUNT_FACTOR
        
        # History tracking
        self.promise_history = []
        self.merit_history = defaultdict(list)
        self.credit_history = defaultdict(list)
        self.detection_history = []
        self.assessments_total = 0 # For tracking total assessments for detection probability
        self.current_round = 0 # Initialize current_round
        self.total_simulation_rounds = 0 # To store the total rounds for global keeping rate

        # Adaptive detection parameters
        self.domain_error_rates = {domain: 0.1 for domain in self.domains}
        # Adaptive detection parameters
        # Initialize detection thresholds with SPRT-style boundary (log(1/alpha))
        initial_threshold = np.log(1 / 0.01) # alpha = 0.01 as per playbook
        self.detection_thresholds = {domain: initial_threshold for domain in self.domains}
        
        # Initialize agents
        self.agents = self._initialize_agents()
        
    def _initialize_agents(self) -> Dict[int, Agent]:
        """Initialize agents with random starting conditions"""
        agents = {}
        for i in range(self.n_agents):
            # Most agents are honest, some are dishonest
            honesty_rate = np.random.choice([0.9, 0.3], p=[0.8, 0.2])
            
            agent = Agent(
                id=i,
                credits=self.base_stake * 100,  # Starting credits based on base_stake
                honesty_rate=honesty_rate,
                external_payoff_mult=np.random.uniform(1.0, 3.0) # Random external payoff multiplier
            )
            
            # Initialize with small random merit in each domain
            for domain in self.domains:
                agent.merit[domain] = np.random.uniform(0.1, 0.3)
                
            agents[i] = agent
            
        return agents
    
    def calculate_stake_requirement(self, agent: Agent, domain: str, promise_value: float) -> float:
        """Calculate stake requirement based on merit and promise value (Improved version)"""
        merit = agent.get_merit(domain)
        # w(m) = m^1.5 * 0.8 for super-linear merit benefit
        discount = (merit ** 1.5) * 0.8
        
        # Stake grows super-linearly with promise value
        base_requirement = self.base_stake * (1 + (promise_value/100)**1.6)
        
        return base_requirement * (1 - discount)
    
    def calculate_promise_value(self, domain: str) -> float:
        """Generate a random promise value"""
        # Promise value can vary by domain
        return np.random.gamma(2, 50) * (1 + hash(domain) % 5) / 5

    def calculate_external_payoff(self, agent: Agent, promise_value: float) -> float:
        """Calculate potential external payoff from breaking promise"""
        base_external = promise_value * agent.external_payoff_mult
        # Add heavy-tailed randomness (log-normal)
        noise = lognorm.rvs(s=0.5, scale=1.0)
        return base_external * noise
    
    def should_keep_promise(self, agent: Agent, domain: str, stake: float, promise_value: float) -> bool:
        """Determine if agent should keep promise based on utility calculation"""
        # Operational cost is 10% of stake
        c_op = stake * 0.1
        
        # Merit changes
        merit = agent.get_merit(domain)
        delta_m_plus = self.gamma * (1 - merit)
        delta_m_minus = -self.lambda_penalty * self.gamma * merit
        
        # Future opportunity value
        fov_diff = self.calculate_fov_difference(agent, domain, delta_m_plus, delta_m_minus)
        
        # Utility calculation from Theorem 1
        # Internal gain from breaking promise (e.g., 20% of promise value)
        internal_gain = promise_value * 0.05
        external_gain = self.calculate_external_payoff(agent, promise_value)
        total_gain = internal_gain + external_gain

        keep_utility = self.alpha * (-c_op) + self.beta * delta_m_plus + fov_diff
        break_utility = self.alpha * (total_gain - stake) + self.beta * delta_m_minus
        
        # Add noise for bounded rationality
        if random.random() < agent.honesty_rate:
            return keep_utility > break_utility
        else:
            return random.random() < 0.5
    
    def calculate_fov_difference(self, agent: Agent, domain: str, delta_plus: float, delta_minus: float) -> float:
        """Calculate difference in future opportunity value"""
        current_merit = agent.get_merit(domain)
        
        # Simplified FOV calculation over next 10 rounds (using params.DISCOUNT_FACTOR)
        fov_keep = sum(params.DISCOUNT_FACTOR**i * self.base_stake * 0.8 * (current_merit + delta_plus) 
                      for i in range(10))
        fov_break = sum(params.DISCOUNT_FACTOR**i * self.base_stake * 0.8 * (current_merit + delta_minus) 
                       for i in range(10))
        
        return self.alpha * (fov_keep - fov_break)
    
    def adaptive_martingale_test(self, promise: Promise, domain: str) -> Tuple[float, bool]:
        """Adaptive martingale test for manipulation detection"""
        assessments = [outcome for _, outcome in promise.assessments]
        
        if not assessments:
            return 0.0, False
        
        # Get current domain error rate estimate
        alpha = 0.05            # desired false-positive rate
        expected_error = max(1e-4, self.domain_error_rates[domain])  # floor at 0.0001

        # Bias-corrected counts (Jeffreys prior for Bernoulli)
        n_errors = sum(1 for a in assessments if a != promise.actual_outcome) + 0.5
        n_total = len(assessments) + 1
        observed_error = n_errors / n_total
        
        # KL-divergence form (numerically stable)
        # Add a small epsilon to prevent log(0) or log of negative numbers
        epsilon = 1e-9
        observed_error = np.clip(observed_error, epsilon, 1 - epsilon)
        expected_error = np.clip(expected_error, epsilon, 1 - epsilon)

        kl = observed_error * np.log(observed_error / expected_error) + \
             (1 - observed_error) * np.log((1 - observed_error) / (1 - expected_error))
        llr = n_total * kl
        
        # SPRT-style boundary
        threshold = self.detection_thresholds[domain]
        
        # Detection decision
        manipulation_detected = llr > threshold
        
        # Update domain error rate with exponential smoothing
        self.domain_error_rates[domain] = 0.9 * expected_error + 0.1 * observed_error
        
        # Detection probability for logging, ensuring it's within [0, 1]
        p_detect = np.clip(1 - np.exp(-llr / threshold), 0, 1) if threshold > 0 else 0
        
        return p_detect, manipulation_detected
    
    def simulate_round(self):
        """Simulate one round of promise-making and assessment"""
        round_promises = []
        
        # Each agent makes promises in random domains
        for agent_id, agent in self.agents.items():
            # Add base income to keep honest agents solvent
            agent.credits += params.BASE_INCOME_PER_ROUND * self.base_stake

            # Add credit top-ups only for agents that kept their last promise and now have < 2*base_stake
            if agent.last_outcome == True and agent.credits < 2 * self.base_stake:
                agent.credits += self.base_stake * 0.5   # loyalty dividend

            if agent.credits < 50:  # Skip if too few credits
                continue
                
            # Choose random domain
            domain = random.choice(self.domains)
            
            # Generate promise value
            promise_value = self.calculate_promise_value(domain)

            # Calculate stake requirement
            stake = self.calculate_stake_requirement(agent, domain, promise_value)
            
            if agent.credits < stake:
                continue
                
            # Decide whether to keep promise
            will_keep = self.should_keep_promise(agent, domain, stake, promise_value)
            
            # Create promise
            promise = Promise(
                promiser_id=agent_id,
                domain=domain,
                stake=stake,
                value=promise_value,
                actual_outcome=will_keep,
                round_num=self.current_round # Pass the current round number
            )
            
            # Deduct stake
            agent.credits -= stake
            
            round_promises.append(promise)
        
        # Assessment phase
        for promise in round_promises:
            # Random assessors (excluding promiser)
            potential_assessors = [a for a in self.agents.keys() if a != promise.promiser_id]
            
            # Scale assessor sample size with n_agents (Phase 1, point 3)
            n_assessors = max(
                5,
                int(self.n_agents * params.ASSESSOR_FRACTION)  # 10 % by default
            )
            n_assessors = min(n_assessors, len(potential_assessors)) # Ensure not more than available

            if n_assessors == 0:
                continue

            assessors = random.sample(potential_assessors, n_assessors)
            self.assessments_total += n_assessors # Track total assessments
            
            for assessor_id in assessors:
                assessor = self.agents[assessor_id]
                
                # Honest assessment with noise
                if random.random() < assessor.honesty_rate:
                    # Honest assessment with small error
                    assessment = promise.actual_outcome if random.random() > 0.1 else not promise.actual_outcome
                else:
                    # Dishonest assessment (possibly coordinated if in coalition)
                    if assessor.coalition_member:
                        assessment = False  # Coordinated negative assessment
                    else:
                        assessment = random.choice([True, False])
                
                promise.assessments.append((assessor_id, assessment))
        
        # Process outcomes
        for promise in round_promises:
            self._process_promise_outcome(promise)
            
        self.promise_history.extend(round_promises)
    
    def _process_promise_outcome(self, promise: Promise):
        """Process promise outcome and update agent states"""
        promiser = self.agents[promise.promiser_id]
        
        # Determine consensus
        if promise.assessments:
            positive_assessments = sum(1 for _, assessment in promise.assessments if assessment)
            consensus = positive_assessments / len(promise.assessments) >= 0.6
        else:
            consensus = promise.actual_outcome
        
        # Check for manipulation using adaptive martingale test
        p_detect, manipulation_detected = self.adaptive_martingale_test(promise, promise.domain)
        
        if manipulation_detected and consensus != promise.actual_outcome:
            self.detection_history.append({
                'round': len(self.promise_history),
                'promise_id': id(promise),
                'detection_probability': p_detect,
                'domain': promise.domain
            })
        
        # Update promiser
        if promise.actual_outcome:
            # Promise kept
            c_op = promise.stake * 0.1
            promiser.credits += (promise.stake - c_op)  # Return stake minus operational cost
            
            # Merit increase
            delta_merit = self.gamma * (1 - promiser.get_merit(promise.domain))
            promiser.update_merit(promise.domain, delta_merit)
        else:
            # Promise broken - stake is lost
            # Merit decrease
            delta_merit = -self.lambda_penalty * self.gamma * promiser.get_merit(promise.domain)
            promiser.update_merit(promise.domain, delta_merit)
        
        promiser.last_outcome = promise.actual_outcome # Update last_outcome for the promiser

        # Update assessors
        for assessor_id, assessment in promise.assessments:
            assessor = self.agents[assessor_id]
            
            # Reward/penalize based on alignment with actual outcome
            if assessment == promise.actual_outcome:
                assessor.credits += 5  # Small reward
                assessor.update_merit(promise.domain, 0.01)
            else:
                assessor.credits -= 10  # Penalty
                assessor.update_merit(promise.domain, -0.02)
    
    def form_coalition(self, size: int, target_domain: str):
        """Form a dishonest coalition"""
        # Select coalition members (prefer low-merit agents)
        agents_by_merit = sorted(self.agents.items(), 
                               key=lambda x: x[1].get_merit(target_domain))
        
        for i in range(min(size, len(agents_by_merit))):
            agent_id, agent = agents_by_merit[i]
            agent.coalition_member = True
            agent.honesty_rate = 0.1  # Become dishonest
        
        # Escalate sensitivity with coalition size
        for d in self.domains:
            self.detection_thresholds[d] *= 0.3**(size/10)
            self.detection_thresholds[d] = max(0.02, self.detection_thresholds[d])
    
    def record_history(self):
        """Record current state for analysis"""
        for agent_id, agent in self.agents.items():
            self.credit_history[agent_id].append(agent.credits)
            
            avg_merit = np.mean(list(agent.merit.values())) if agent.merit else 0
            self.merit_history[agent_id].append(avg_merit)
    
    def run_simulation(self, n_rounds: int, coalition_round: Optional[int] = None, 
                      coalition_size: int = 10):
        """Run the full simulation"""
        self.total_simulation_rounds = n_rounds # Store total rounds
        for round_num in range(n_rounds):
            self.current_round = round_num # Update current_round
            # Form coalition at specified round
            if coalition_round and round_num == coalition_round:
                target_domain = random.choice(self.domains)
                self.form_coalition(coalition_size, target_domain)
                print(f"Coalition formed at round {round_num} targeting {target_domain}")
            
            self.simulate_round()
            self.record_history()
            
            if round_num % 10 == 0:
                avg_merit = np.mean([np.mean(list(a.merit.values())) 
                                   for a in self.agents.values() if a.merit])
                avg_credits = np.mean([a.credits for a in self.agents.values()])
                # Filter promises for the current round only
                promises_this_round = [p for p in self.promise_history if p.round_num == round_num]
                num_promises_made_this_round = len(promises_this_round)
                num_agents_made_promise = len(set([p.promiser_id for p in promises_this_round]))

                # Track coalition vs non-coalition metrics separately
                coalition_metrics, honest_metrics = self.get_agent_metrics()
                avg_merit_honest = honest_metrics["avg_merit"]
                avg_merit_coalition = coalition_metrics["avg_merit"]

                print(f"Round {round_num}: Avg Merit={avg_merit:.3f}, Avg Credits={avg_credits:.1f}, Promises this round={num_promises_made_this_round}, Agents made promise={num_agents_made_promise}, Honest Avg Merit={avg_merit_honest:.3f}, Coalition Avg Merit={avg_merit_coalition:.3f}")
    
    def promise_keeping_rate_global(self) -> float:
        """Calculate promise keeping rate over all agents (Phase 2, point 1)"""
        kept_promises = sum(1 for p in self.promise_history if p.actual_outcome)
        total_promises_made = len(self.promise_history)
        return kept_promises / total_promises_made if total_promises_made > 0 else 0

    def get_agent_metrics(self) -> Tuple[Dict, Dict]:
        """Track coalition vs non-coalition metrics separately (Phase 2, point 2)"""
        coalition_agents = [a for a in self.agents.values() if a.coalition_member]
        honest_agents = [a for a in self.agents.values() if not a.coalition_member]

        coalition_metrics = {
            "avg_merit": np.mean([np.mean(list(a.merit.values())) for a in coalition_agents]) if coalition_agents else 0,
            "avg_credits": np.mean([a.credits for a in coalition_agents]) if coalition_agents else 0,
            "num_agents": len(coalition_agents)
        }
        honest_metrics = {
            "avg_merit": np.mean([np.mean(list(a.merit.values())) for a in honest_agents]) if honest_agents else 0,
            "avg_credits": np.mean([a.credits for a in honest_agents]) if honest_agents else 0,
            "num_agents": len(honest_agents)
        }
        return coalition_metrics, honest_metrics

    def analyze_results(self):
        """Analyze simulation results (plotting removed as per instructions)"""
        # Print summary statistics
        print("\n=== Simulation Summary ===")
        print(f"Total promises made: {len(self.promise_history)}")
        
        kept_promises = sum(1 for p in self.promise_history if p.actual_outcome)
        print(f"Promises kept: {kept_promises}/{len(self.promise_history)} "
              f"({kept_promises/len(self.promise_history)*100:.1f}%)")
        
        print(f"Manipulation detections: {len(self.detection_history)}")
        print(f"Total assessments: {self.assessments_total}")
        print(f"Detection probability (detections/total assessments): {len(self.detection_history) / self.assessments_total if self.assessments_total > 0 else 0:.3f}")

        # Analyze equilibrium
        final_merits = [np.mean(list(agent.merit.values())) if agent.merit else 0 
                       for agent in self.agents.values()]
        final_avg_merit = np.mean(final_merits)
        merit_variance = np.var(final_merits)
        print(f"\nFinal average merit: {final_avg_merit:.3f} (variance: {merit_variance:.3f})")
        
        # Check if honest agents outperform dishonest ones
        coalition_metrics, honest_metrics = self.get_agent_metrics()
        
        if honest_metrics["num_agents"] > 0:
            print(f"\nHonest agents ({honest_metrics['num_agents']}) avg merit: {honest_metrics['avg_merit']:.3f}")
            print(f"Honest agents ({honest_metrics['num_agents']}) avg credits: {honest_metrics['avg_credits']:.1f}")
        
        if coalition_metrics["num_agents"] > 0:
            print(f"Coalition agents ({coalition_metrics['num_agents']}) avg merit: {coalition_metrics['avg_merit']:.3f}")
            print(f"Coalition agents ({coalition_metrics['num_agents']}) avg credits: {coalition_metrics['avg_credits']:.1f}")
        
        return {
            'detection_events': len(self.detection_history),
            'promise_keeping_rate_global': self.promise_keeping_rate_global(),
            'final_average_merit': final_avg_merit,
            'merit_variance': merit_variance,
            'detection_probability': len(self.detection_history) / self.assessments_total if self.assessments_total > 0 else 0
        }

    def get_simulation_summary(self, n_rounds: int, coalition_round: Optional[int] = None, coalition_size: int = 10) -> Dict:
        """Runs the simulation and returns a summary of key metrics."""
        self.run_simulation(n_rounds, coalition_round, coalition_size)
        
        kept_promises = sum(1 for p in self.promise_history if p.actual_outcome)
        total_promises = len(self.promise_history)
        
        final_merits = [np.mean(list(agent.merit.values())) if agent.merit else 0 for agent in self.agents.values()]
        final_avg_merit = np.mean(final_merits) if final_merits else 0

        return {
            'n_agents': self.n_agents,
            'n_rounds': n_rounds,
            'coalition_formed': coalition_round is not None,
            'coalition_size': coalition_size if coalition_round else 0,
            'promise_keeping_rate_global': self.promise_keeping_rate_global(),
            'total_promises_made': total_promises,
            'detection_events': len(self.detection_history),
            'assessments_total': self.assessments_total,
            'detection_probability': len(self.detection_history) / self.assessments_total if self.assessments_total > 0 else 0,
            'final_average_merit': final_avg_merit,
            'merit_variance': np.var(final_merits) if final_merits else 0
        }

# Example usage
if __name__ == "__main__":
    from abm.params import BASE_STAKE, GAMMA, LAMBDA_PENALTY, DETECTION_SENSITIVITY, DISCOUNT_FACTOR, ASSESSOR_FRACTION, BASE_INCOME_PER_ROUND

    SCENARIOS = [
        ("baseline", dict(coalition_round=None)),
        ("coalition_5",  dict(coalition_round=500, coalition_size=5)),
        ("coalition_15", dict(coalition_round=500, coalition_size=15)),
        ("coalition_30", dict(coalition_round=500, coalition_size=30)),
    ]

    records = []
    for label, kwargs in SCENARIOS:
        metrics = []
        for seed in range(20):
            sim = AgencyProtocolSimulation(n_rounds=1000, seed=seed) # n_rounds=1000 as per instructions
            sim.run_simulation(n_rounds=1000, **kwargs)
            metrics.append({
                "keeping_rate" : sim.promise_keeping_rate_global(),
                "detect_prob"  : sim.detection_history / sim.assessments_total if sim.assessments_total > 0 else 0,
                "avg_merit"    : np.mean([np.mean(list(a.merit.values())) for a in sim.agents.values()])
            })
        df = pd.DataFrame(metrics)
        records.append({"scenario": label, **df.mean().to_dict()})

    print(json.dumps(records, indent=2))
