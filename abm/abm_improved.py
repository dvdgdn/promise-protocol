import numpy as np
import matplotlib.pyplot as plt
from dataclasses import dataclass, field
from typing import Dict, List, Tuple, Optional, Union
import random
from collections import defaultdict
import pandas as pd
from scipy.special import rel_entr
from scipy.stats import lognorm

@dataclass
class Promise:
    """Represents a promise made by an agent"""
    promiser_id: int
    domain: str
    stake: float
    value: float  # External value of the promise
    actual_outcome: Optional[bool] = None
    assessments: List[Tuple[int, bool]] = field(default_factory=list)
    oracle_verdict: Optional[bool] = None  # Oracle assessment if available
    
@dataclass
class Agent:
    """Represents an agent in the protocol"""
    id: int
    credits: float
    merit: Dict[str, float] = field(default_factory=dict)
    merit_history: List[Dict[str, float]] = field(default_factory=list)  # Track merit changes
    honesty_rate: float = 0.9
    coalition_member: bool = False
    state: str = "normal"  # normal, cooldown, burst_attack
    burst_patience: int = 0  # Rounds until burst attack
    external_payoff_mult: float = 1.0  # External benefit multiplier
    
    def get_merit(self, domain: str) -> float:
        return self.merit.get(domain, 0.0)
    
    def update_merit(self, domain: str, delta: float):
        current = self.get_merit(domain)
        # Merit bounded between 0 and 1
        self.merit[domain] = max(0.0, min(1.0, current + delta))
        # Record history for velocity tracking
        self.merit_history.append({domain: self.merit[domain]})
    
    def get_merit_velocity(self, domain: str, window: int = 5) -> float:
        """Calculate recent merit change velocity"""
        if len(self.merit_history) < 2:
            return 0.0
        
        recent_history = self.merit_history[-window:]
        values = [h.get(domain, 0.0) for h in recent_history]
        
        if len(values) < 2:
            return 0.0
            
        return (values[-1] - values[0]) / len(values)

class ImprovedAgencyProtocolSimulation:
    def __init__(self, 
                 n_agents: int = 100,
                 n_domains: int = 5,
                 base_stake: float = 100.0,
                 alpha: float = 1.0,  # Credit weight in utility
                 beta: float = 2.0,   # Merit weight in utility
                 gamma: float = 0.1,  # Base merit impact
                 lambda_penalty: float = 2.0,  # Penalty multiplier
                 detection_sensitivity: float = 0.5,
                 discount_factor: float = 0.9,
                 seed: Optional[int] = None,
                 risk_aversion: float = 0.5,  # For concave utility
                 oracle_corruption_rate: float = 0.05,
                 merit_velocity_threshold: float = -0.3,  # Merit drop threshold
                 cooldown_rounds: int = 10):
        
        # Set random seed for reproducibility
        if seed is not None:
            np.random.seed(seed)
            random.seed(seed)
        
        self.n_agents = n_agents
        self.n_domains = n_domains
        self.domains = [f"domain_{i}" for i in range(n_domains)]
        
        # Economic parameters
        self.base_stake = base_stake
        self.alpha = alpha
        self.beta = beta
        self.gamma = gamma
        self.lambda_penalty = lambda_penalty
        self.detection_sensitivity = detection_sensitivity
        self.discount_factor = discount_factor
        self.risk_aversion = risk_aversion
        
        # New parameters for improvements
        self.oracle_corruption_rate = oracle_corruption_rate
        self.merit_velocity_threshold = merit_velocity_threshold
        self.cooldown_rounds = cooldown_rounds
        
        # Initialize agents
        self.agents = self._initialize_agents()
        
        # Initialize oracles for each domain
        self.oracles = self._initialize_oracles()
        
        # History tracking
        self.promise_history = []
        self.merit_history = defaultdict(list)
        self.credit_history = defaultdict(list)
        self.detection_history = []
        self.cooldown_history = []
        
        # Adaptive detection parameters
        self.domain_error_rates = {domain: 0.1 for domain in self.domains}
        self.detection_thresholds = {domain: 2.0 for domain in self.domains}
        
    def _initialize_agents(self) -> Dict[int, Agent]:
        """Initialize agents with varied characteristics"""
        agents = {}
        for i in range(self.n_agents):
            # Most agents are honest, some are dishonest, some are burst attackers
            agent_type = np.random.choice(['honest', 'dishonest', 'burst'], p=[0.7, 0.2, 0.1])
            
            if agent_type == 'honest':
                honesty_rate = np.random.uniform(0.8, 0.95)
                external_mult = np.random.uniform(0.8, 1.2)
            elif agent_type == 'dishonest':
                honesty_rate = np.random.uniform(0.2, 0.4)
                external_mult = np.random.uniform(1.5, 2.5)  # Higher external incentives
            else:  # burst attacker
                honesty_rate = 0.9  # Starts honest
                external_mult = np.random.uniform(2.0, 3.0)
                
            agent = Agent(
                id=i,
                credits=1000.0,
                honesty_rate=honesty_rate,
                external_payoff_mult=external_mult,
                burst_patience=np.random.randint(20, 60) if agent_type == 'burst' else 0
            )
            
            # Initialize with small random merit in each domain
            for domain in self.domains:
                agent.merit[domain] = np.random.uniform(0.1, 0.3)
                
            agents[i] = agent
            
        return agents
    
    def _initialize_oracles(self) -> Dict[str, List['OracleAgent']]:
        """Initialize oracle agents for each domain"""
        oracles = {}
        for domain in self.domains:
            # 3-5 oracles per domain
            n_oracles = np.random.randint(3, 6)
            domain_oracles = []
            
            for i in range(n_oracles):
                oracle = OracleAgent(
                    id=f"oracle_{domain}_{i}",
                    domain=domain,
                    accuracy=np.random.uniform(0.85, 0.95),
                    is_corrupt=random.random() < self.oracle_corruption_rate
                )
                domain_oracles.append(oracle)
                
            oracles[domain] = domain_oracles
            
        return oracles
    
    def concave_utility(self, wealth: float) -> float:
        """Concave utility function modeling risk aversion"""
        if wealth <= 0:
            return -1000  # Large negative utility for bankruptcy
        
        # Log utility with risk aversion parameter
        return (1 - self.risk_aversion) * wealth + self.risk_aversion * np.log(wealth + 1)
    
    def calculate_stake_requirement(self, agent: Agent, domain: str, promise_value: float) -> float:
        """Calculate stake requirement based on merit and promise value"""
        merit = agent.get_merit(domain)
        
        # Check if agent is in cooldown
        if agent.state == 'cooldown':
            discount = 0  # No discount during cooldown
        else:
            # w(m) = m^1.5 * 0.8 for super-linear merit benefit
            discount = (merit ** 1.5) * 0.8
        
        # Stake grows super-linearly with promise value (addresses external payoff issue)
        base_requirement = self.base_stake * (1 + np.log(1 + promise_value / 100))
        
        return base_requirement * (1 - discount)
    
    def calculate_external_payoff(self, agent: Agent, promise_value: float) -> float:
        """Calculate potential external payoff from breaking promise"""
        # External payoff can be much larger than internal gain
        # Models things like short-selling, reputation arbitrage, etc.
        base_external = promise_value * agent.external_payoff_mult
        
        # Add heavy-tailed randomness (log-normal)
        noise = lognorm.rvs(s=0.5, scale=1.0)
        
        return base_external * noise
    
    def should_keep_promise(self, agent: Agent, domain: str, stake: float, 
                          promise_value: float) -> bool:
        """Determine if agent should keep promise using concave utility"""
        # Check for burst attack timing
        if agent.state == 'normal' and agent.burst_patience > 0:
            agent.burst_patience -= 1
            if agent.burst_patience == 0:
                agent.state = 'burst_attack'
                agent.honesty_rate = 0.1  # Become dishonest
        
        # Operational cost
        c_op = stake * 0.1
        
        # Merit changes with sigmoid impact function
        merit = agent.get_merit(domain)
        # Sigmoid merit impact to prevent Sybil exploitation
        merit_factor = 1 / (1 + np.exp(-10 * (merit - 0.5)))
        
        delta_m_plus = self.gamma * (1 - merit) * merit_factor
        delta_m_minus = -self.lambda_penalty * self.gamma * merit * merit_factor
        
        # Calculate utilities using concave function
        current_wealth = agent.credits
        
        # Utility of keeping promise
        wealth_keep = current_wealth - c_op
        fov_keep = self.calculate_fov_difference(agent, domain, delta_m_plus, 0)
        utility_keep = self.concave_utility(wealth_keep) + self.beta * delta_m_plus + fov_keep
        
        # Utility of breaking promise (including external payoff)
        internal_gain = promise_value * 0.2  # 20% internal gain
        external_gain = self.calculate_external_payoff(agent, promise_value)
        total_gain = internal_gain + external_gain
        
        wealth_break = current_wealth + total_gain - stake
        fov_break = self.calculate_fov_difference(agent, domain, 0, delta_m_minus)
        utility_break = self.concave_utility(wealth_break) + self.beta * delta_m_minus + fov_break
        
        # Decision with bounded rationality
        if agent.state == 'burst_attack' or (agent.coalition_member and random.random() < 0.8):
            return False  # Coordinated defection
        elif random.random() < agent.honesty_rate:
            return utility_keep > utility_break
        else:
            return random.random() < 0.5
    
    def calculate_fov_difference(self, agent: Agent, domain: str, 
                                delta_plus: float, delta_minus: float) -> float:
        """Calculate difference in future opportunity value"""
        current_merit = agent.get_merit(domain)
        future_merit_keep = min(1.0, current_merit + delta_plus)
        future_merit_break = max(0.0, current_merit + delta_minus)
        
        # Expected future benefits over next rounds
        fov_keep = 0
        fov_break = 0
        
        for i in range(10):
            # Expected promise value distribution
            expected_value = np.random.gamma(2, 50)
            
            # Future stake requirements
            stake_keep = self.calculate_stake_requirement(agent, domain, expected_value)
            stake_break = self.calculate_stake_requirement(agent, domain, expected_value)
            
            # Discounted expected profit
            profit_keep = expected_value * 0.1 - stake_keep * 0.1  # Expected profit margin
            profit_break = expected_value * 0.1 - stake_break * 0.1
            
            fov_keep += self.discount_factor**i * profit_keep * future_merit_keep
            fov_break += self.discount_factor**i * profit_break * future_merit_break
        
        return self.alpha * (fov_keep - fov_break)
    
    def adaptive_martingale_test(self, promise: Promise, domain: str) -> Tuple[float, bool]:
        """Adaptive martingale test for manipulation detection"""
        assessments = [outcome for _, outcome in promise.assessments]
        
        if not assessments:
            return 0.0, False
        
        # Get current domain error rate estimate
        expected_error = self.domain_error_rates[domain]
        
        # Calculate log-likelihood ratio statistic
        n_errors = sum(1 for a in assessments if a != promise.actual_outcome)
        n_total = len(assessments)
        observed_error = n_errors / n_total if n_total > 0 else 0
        
        # Martingale process for sequential testing
        if observed_error > 0 and expected_error > 0:
            # Log likelihood ratio
            llr = n_errors * np.log(observed_error / expected_error) + \
                  (n_total - n_errors) * np.log((1 - observed_error) / (1 - expected_error))
        else:
            llr = 0
        
        # Update domain error rate with exponential smoothing
        self.domain_error_rates[domain] = 0.9 * expected_error + 0.1 * observed_error
        
        # Adaptive threshold based on sample size
        threshold = self.detection_thresholds[domain] * np.sqrt(np.log(n_total + 2))
        
        # Detection decision
        manipulation_detected = llr > threshold
        
        # Update threshold based on detection history
        if manipulation_detected:
            self.detection_thresholds[domain] *= 0.95  # Make more sensitive
        else:
            self.detection_thresholds[domain] *= 1.01  # Make less sensitive
        
        # Detection probability for logging
        p_detect = 1 - np.exp(-llr / threshold) if llr > 0 else 0
        
        return p_detect, manipulation_detected
    
    def simulate_round(self):
        """Simulate one round of promise-making and assessment"""
        round_promises = []
        
        # Update agent states
        for agent in self.agents.values():
            # Check cooldown expiry
            if agent.state == 'cooldown':
                agent.burst_patience -= 1
                if agent.burst_patience <= 0:
                    agent.state = 'normal'
        
        # Each agent makes promises
        for agent_id, agent in self.agents.items():
            if agent.credits < 50:  # Skip if too few credits
                continue
                
            # Choose random domain
            domain = random.choice(self.domains)
            
            # Generate promise value (varies by domain)
            promise_value = np.random.gamma(2, 50) * (1 + hash(domain) % 5) / 5
            
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
                actual_outcome=will_keep
            )
            
            # Deduct stake
            agent.credits -= stake
            
            round_promises.append(promise)
        
        # Assessment phase
        for promise in round_promises:
            # Oracle assessment with value-at-risk staking
            oracle_assessments = []
            for oracle in self.oracles[promise.domain]:
                oracle_stake = promise.value * 0.05  # 5% of promise value
                oracle_assessment = oracle.assess(promise.actual_outcome)
                oracle_assessments.append(oracle_assessment)
            
            # Use majority oracle verdict if available
            if oracle_assessments:
                promise.oracle_verdict = sum(oracle_assessments) > len(oracle_assessments) / 2
            
            # Peer assessments
            potential_assessors = [a for a in self.agents.keys() if a != promise.promiser_id]
            n_assessors = min(5, len(potential_assessors))
            assessors = random.sample(potential_assessors, n_assessors)
            
            for assessor_id in assessors:
                assessor = self.agents[assessor_id]
                
                # Assessment logic
                if random.random() < assessor.honesty_rate:
                    # Honest assessment with small error
                    assessment = promise.actual_outcome if random.random() > 0.1 else not promise.actual_outcome
                else:
                    # Dishonest assessment
                    if assessor.coalition_member or assessor.state == 'burst_attack':
                        # Coordinated false assessment
                        assessment = False
                    else:
                        assessment = random.choice([True, False])
                
                promise.assessments.append((assessor_id, assessment))
        
        # Process outcomes
        for promise in round_promises:
            self._process_promise_outcome(promise)
            
        self.promise_history.extend(round_promises)
    
    def _process_promise_outcome(self, promise: Promise):
        """Process promise outcome with improved mechanisms"""
        promiser = self.agents[promise.promiser_id]
        
        # Use oracle verdict if available, otherwise peer consensus
        if promise.oracle_verdict is not None:
            consensus = promise.oracle_verdict
        else:
            if promise.assessments:
                positive_assessments = sum(1 for _, assessment in promise.assessments if assessment)
                consensus = positive_assessments / len(promise.assessments) >= 0.6
            else:
                consensus = promise.actual_outcome
        
        # Adaptive manipulation detection
        p_detect, manipulation_detected = self.adaptive_martingale_test(promise, promise.domain)
        
        if manipulation_detected and consensus != promise.actual_outcome:
            self.detection_history.append({
                'round': len(self.promise_history),
                'promise_id': id(promise),
                'detection_probability': p_detect,
                'domain': promise.domain
            })
            
            # Penalize manipulators
            for assessor_id, assessment in promise.assessments:
                if assessment != promise.actual_outcome:
                    assessor = self.agents[assessor_id]
                    assessor.credits -= 50  # Heavy penalty
                    assessor.update_merit(promise.domain, -0.1)
        
        # Track merit before update
        merit_before = promiser.get_merit(promise.domain)
        
        # Update promiser
        if promise.actual_outcome:
            # Promise kept
            c_op = promise.stake * 0.1
            promiser.credits += (promise.stake - c_op)
            
            # Merit increase with sigmoid
            merit_factor = 1 / (1 + np.exp(-10 * (merit_before - 0.5)))
            delta_merit = self.gamma * (1 - merit_before) * merit_factor
            promiser.update_merit(promise.domain, delta_merit)
        else:
            # Promise broken - stake is lost
            # Merit decrease with sigmoid
            merit_factor = 1 / (1 + np.exp(-10 * (merit_before - 0.5)))
            delta_merit = -self.lambda_penalty * self.gamma * merit_before * merit_factor
            promiser.update_merit(promise.domain, delta_merit)
        
        # Check merit velocity for cooldown trigger
        merit_velocity = promiser.get_merit_velocity(promise.domain)
        if merit_velocity < self.merit_velocity_threshold:
            promiser.state = 'cooldown'
            promiser.burst_patience = self.cooldown_rounds
            self.cooldown_history.append({
                'round': len(self.promise_history),
                'agent_id': promiser.id,
                'merit_drop': merit_velocity
            })
        
        # Update assessors
        for assessor_id, assessment in promise.assessments:
            assessor = self.agents[assessor_id]
            
            # Reward/penalize based on alignment with actual outcome
            if assessment == promise.actual_outcome:
                assessor.credits += 5
                assessor.update_merit(promise.domain, 0.01)
            else:
                assessor.credits -= 10
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
    
    def record_history(self):
        """Record current state for analysis"""
        for agent_id, agent in self.agents.items():
            self.credit_history[agent_id].append(agent.credits)
            
            avg_merit = np.mean(list(agent.merit.values())) if agent.merit else 0
            self.merit_history[agent_id].append(avg_merit)
    
    def run_simulation(self, n_rounds: int, coalition_round: Optional[int] = None, 
                      coalition_size: int = 10):
        """Run the full simulation"""
        for round_num in range(n_rounds):
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
                n_cooldown = sum(1 for a in self.agents.values() if a.state == 'cooldown')
                print(f"Round {round_num}: Avg Merit={avg_merit:.3f}, "
                      f"Avg Credits={avg_credits:.1f}, Cooldown agents={n_cooldown}")
    
    def analyze_results(self):
        """Analyze and visualize simulation results"""
        fig, axes = plt.subplots(3, 2, figsize=(16, 14))
        
        # 1. Average merit over time
        ax = axes[0, 0]
        avg_merit_history = []
        for i in range(len(self.merit_history[0])):
            avg_merit = np.mean([self.merit_history[agent_id][i] 
                               for agent_id in self.merit_history])
            avg_merit_history.append(avg_merit)
        
        ax.plot(avg_merit_history, linewidth=2)
        ax.set_title('Average Merit Evolution', fontsize=14)
        ax.set_xlabel('Round')
        ax.set_ylabel('Average Merit')
        ax.grid(True, alpha=0.3)
        
        # 2. Credit distribution
        ax = axes[0, 1]
        final_credits = [agent.credits for agent in self.agents.values()]
        ax.hist(final_credits, bins=30, alpha=0.7, edgecolor='black')
        ax.set_title('Final Credit Distribution', fontsize=14)
        ax.set_xlabel('Credits')
        ax.set_ylabel('Number of Agents')
        ax.grid(True, alpha=0.3)
        
        # 3. Honesty rate vs final merit
        ax = axes[1, 0]
        honesty_rates = [agent.honesty_rate for agent in self.agents.values()]
        final_merits = [np.mean(list(agent.merit.values())) if agent.merit else 0 
                       for agent in self.agents.values()]
        colors = ['red' if agent.state == 'cooldown' else 'blue' 
                 for agent in self.agents.values()]
        
        ax.scatter(honesty_rates, final_merits, alpha=0.5, c=colors)
        ax.set_title('Honesty Rate vs Final Merit (red=cooldown)', fontsize=14)
        ax.set_xlabel('Honesty Rate')
        ax.set_ylabel('Final Average Merit')
        ax.grid(True, alpha=0.3)
        
        # 4. Adaptive detection events
        ax = axes[1, 1]
        if self.detection_history:
            detection_rounds = [d['round'] for d in self.detection_history]
            detection_probs = [d['detection_probability'] for d in self.detection_history]
            
            ax.scatter(detection_rounds, detection_probs, alpha=0.6, color='red')
            ax.set_title('Adaptive Manipulation Detection', fontsize=14)
            ax.set_xlabel('Round')
            ax.set_ylabel('Detection Probability')
            ax.set_ylim(0, 1)
        else:
            ax.text(0.5, 0.5, 'No manipulations detected', 
                   transform=ax.transAxes, ha='center', va='center')
            ax.set_title('Adaptive Manipulation Detection', fontsize=14)
        ax.grid(True, alpha=0.3)
        
        # 5. Merit velocity and cooldowns
        ax = axes[2, 0]
        if self.cooldown_history:
            cooldown_rounds = [c['round'] for c in self.cooldown_history]
            merit_drops = [c['merit_drop'] for c in self.cooldown_history]
            
            ax.scatter(cooldown_rounds, merit_drops, alpha=0.6, color='orange')
            ax.axhline(y=self.merit_velocity_threshold, color='red', linestyle='--', 
                      label='Cooldown threshold')
            ax.set_title('Merit Velocity Triggers', fontsize=14)
            ax.set_xlabel('Round')
            ax.set_ylabel('Merit Velocity')
            ax.legend()
        else:
            ax.text(0.5, 0.5, 'No cooldown triggers', 
                   transform=ax.transAxes, ha='center', va='center')
            ax.set_title('Merit Velocity Triggers', fontsize=14)
        ax.grid(True, alpha=0.3)
        
        # 6. Domain error rates over time
        ax = axes[2, 1]
        for domain in self.domains[:3]:  # Show first 3 domains
            error_history = []
            for i in range(0, len(self.promise_history), 10):
                promises = [p for p in self.promise_history[i:i+10] if p.domain == domain]
                if promises:
                    errors = sum(1 for p in promises 
                               for _, a in p.assessments if a != p.actual_outcome)
                    total = sum(len(p.assessments) for p in promises)
                    error_rate = errors / total if total > 0 else 0
                    error_history.append(error_rate)
            
            if error_history:
                ax.plot(range(0, len(error_history) * 10, 10), error_history, 
                       label=domain, alpha=0.7)
        
        ax.set_title('Domain Error Rates (Adaptive)', fontsize=14)
        ax.set_xlabel('Round')
        ax.set_ylabel('Error Rate')
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        plt.tight_layout()
        plt.show()
        
        # Print enhanced summary statistics
        print("\n=== Enhanced Simulation Summary ===")
        print(f"Total promises made: {len(self.promise_history)}")
        
        kept_promises = sum(1 for p in self.promise_history if p.actual_outcome)
        print(f"Promises kept: {kept_promises}/{len(self.promise_history)} "
              f"({kept_promises/len(self.promise_history)*100:.1f}%)")
        
        print(f"Manipulation detections: {len(self.detection_history)}")
        print(f"Cooldown triggers: {len(self.cooldown_history)}")
        
        # Analyze equilibrium
        final_avg_merit = np.mean(final_merits)
        merit_variance = np.var(final_merits)
        print(f"\nFinal average merit: {final_avg_merit:.3f} (variance: {merit_variance:.3f})")
        
        # Check honest vs dishonest performance
        honest_agents = [a for a in self.agents.values() if a.honesty_rate > 0.5]
        dishonest_agents = [a for a in self.agents.values() if a.honesty_rate <= 0.5]
        burst_agents = [a for a in self.agents.values() if a.state == 'burst_attack']
        
        if honest_agents:
            honest_avg_merit = np.mean([np.mean(list(a.merit.values())) if a.merit else 0 
                                       for a in honest_agents])
            honest_avg_credits = np.mean([a.credits for a in honest_agents])
            print(f"\nHonest agents ({len(honest_agents)}): "
                  f"merit={honest_avg_merit:.3f}, credits={honest_avg_credits:.1f}")
        
        if dishonest_agents:
            dishonest_avg_merit = np.mean([np.mean(list(a.merit.values())) if a.merit else 0 
                                         for a in dishonest_agents])
            dishonest_avg_credits = np.mean([a.credits for a in dishonest_agents])
            print(f"Dishonest agents ({len(dishonest_agents)}): "
                  f"merit={dishonest_avg_merit:.3f}, credits={dishonest_avg_credits:.1f}")
        
        if burst_agents:
            burst_avg_merit = np.mean([np.mean(list(a.merit.values())) if a.merit else 0 
                                     for a in burst_agents])
            burst_avg_credits = np.mean([a.credits for a in burst_agents])
            print(f"Burst attack agents ({len(burst_agents)}): "
                  f"merit={burst_avg_merit:.3f}, credits={burst_avg_credits:.1f}")
        
        # Utility analysis
        print("\n=== Utility Analysis (Concave) ===")
        sample_agents = list(self.agents.values())[:5]
        for agent in sample_agents:
            utility = self.concave_utility(agent.credits)
            print(f"Agent {agent.id}: credits={agent.credits:.1f}, utility={utility:.2f}")
        
        return {
            'avg_merit_history': avg_merit_history,
            'final_credits': final_credits,
            'detection_events': len(self.detection_history),
            'cooldown_events': len(self.cooldown_history),
            'promise_keeping_rate': kept_promises/len(self.promise_history) if self.promise_history else 0
        }

class OracleAgent:
    """Oracle agent for ground truth assessment"""
    def __init__(self, id: str, domain: str, accuracy: float = 0.9, is_corrupt: bool = False):
        self.id = id
        self.domain = domain
        self.accuracy = accuracy
        self.is_corrupt = is_corrupt
        self.credits = 10000  # Oracles have large credit reserves
        
    def assess(self, true_outcome: bool) -> bool:
        """Provide assessment with possible corruption"""
        if self.is_corrupt:
            # Corrupt oracle provides false assessment
            return not true_outcome
        else:
            # Honest oracle with accuracy rate
            return true_outcome if random.random() < self.accuracy else not true_outcome

# Example usage
if __name__ == "__main__":
    print("=== Improved Agency Protocol Simulation ===\n")
    
    # Run simulation with fixed seed for reproducibility
    print("Scenario 1: Normal operation with improved mechanisms")
    sim1 = ImprovedAgencyProtocolSimulation(
        n_agents=100, 
        n_domains=5,
        seed=42,
        risk_aversion=0.5,
        merit_velocity_threshold=-0.3
    )
    sim1.run_simulation(n_rounds=150)
    results1 = sim1.analyze_results()
    
    # Run simulation with coalition attack
    print("\n\nScenario 2: Coalition attack with adaptive detection")
    sim2 = ImprovedAgencyProtocolSimulation(
        n_agents=100, 
        n_domains=5,
        seed=43,
        risk_aversion=0.5,
        merit_velocity_threshold=-0.3
    )
    sim2.run_simulation(n_rounds=150, coalition_round=50, coalition_size=20)
    results2 = sim2.analyze_results()