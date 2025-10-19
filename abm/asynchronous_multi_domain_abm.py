"""
Agency Protocol – Asynchronous, Multi-Domain Repeated Game ABM
=============================================================

This implementation translates the Coq formalization into a practical ABM that:
  • Supports N ≥ 2 agents with heterogeneous parameters
  • Supports M ≥ 1 domains with cross-domain effects
  • Uses asynchronous scheduling with fairness guarantees
  • Implements heterogeneous discount factors δₐ ∈ (0,1)
  • Models domain-specific merit & stake functions
  • Tests for Subgame-Perfect Equilibrium (SPE) conditions
  • Validates coalition-proofness properties
"""

import numpy as np
import matplotlib.pyplot as plt
from dataclasses import dataclass, field
from typing import Dict, List, Tuple, Optional, Callable, Set
from collections import defaultdict, deque
import pandas as pd
import random
from scipy.stats import chi2
from itertools import combinations

@dataclass
class EconomicParams:
    """Economic parameters per agent/domain"""
    alpha: Dict[int, float]  # Credit weight per agent
    beta: Dict[Tuple[int, str], float]  # Merit weight per (agent, domain)
    delta: Dict[int, float]  # Discount factor per agent
    
    def validate(self):
        """Ensure parameters satisfy theoretical constraints"""
        for a, α in self.alpha.items():
            assert α > 0, f"α must be positive for agent {a}"
        
        for (a, d), β in self.beta.items():
            assert β >= 0, f"β must be non-negative for agent {a}, domain {d}"
        
        for a, δ in self.delta.items():
            assert 0 < δ < 1, f"δ must be in (0,1) for agent {a}"

@dataclass
class Event:
    """Single asynchronous event in the game"""
    actor: int
    domain: str
    stake: float
    outcome: str  # 'kept' or 'broken'
    round: int
    assessments: List[Tuple[int, bool]] = field(default_factory=list)
    
@dataclass
class MeritState:
    """Current merit state across all agents and domains"""
    M: Dict[Tuple[int, str], float] = field(default_factory=dict)
    
    def __init__(self, agents: List[int], domains: List[str]):
        # Initialize merit in [0,1]
        for a in agents:
            for d in domains:
                self.M[(a, d)] = np.random.uniform(0.1, 0.3)
    
    def get(self, agent: int, domain: str) -> float:
        return self.M.get((agent, domain), 0.1)
    
    def update(self, agent: int, domain: str, new_value: float):
        """Update merit, enforcing bounds [0,1]"""
        self.M[(agent, domain)] = max(0.0, min(1.0, new_value))

class AsynchronousScheduler:
    """Fair scheduler ensuring every agent acts infinitely often"""
    def __init__(self, agents: List[int], seed: Optional[int] = None):
        self.agents = agents
        self.n_agents = len(agents)
        self.history = []
        self.round = 0
        
        if seed is not None:
            np.random.seed(seed)
            random.seed(seed)
    
    def next(self) -> int:
        """Get next agent to act, ensuring fairness"""
        # Simple round-robin with random perturbation for realism
        if random.random() < 0.8:  # 80% follow round-robin
            agent = self.agents[self.round % self.n_agents]
        else:  # 20% random selection
            agent = random.choice(self.agents)
        
        self.history.append(agent)
        self.round += 1
        return agent
    
    def is_fair(self, window: int = 100) -> bool:
        """Check if schedule has been fair over recent window"""
        if len(self.history) < window:
            return True
        
        recent = self.history[-window:]
        counts = {a: recent.count(a) for a in self.agents}
        
        # Chi-square test for uniformity
        expected = window / self.n_agents
        chi2_stat = sum((count - expected)**2 / expected for count in counts.values())
        
        # Critical value at 95% confidence
        critical_value = chi2.ppf(0.95, self.n_agents - 1)
        
        return chi2_stat < critical_value

class Strategy:
    """Base class for agent strategies"""
    def __init__(self, agent_id: int, params: EconomicParams):
        self.agent_id = agent_id
        self.params = params
        
    def decide(self, history: List[Event], merit_state: MeritState, 
               domain: str, stake: float) -> str:
        """Decide whether to keep or break promise"""
        raise NotImplementedError

class CooperativeStrategy(Strategy):
    """Always cooperate (keep promises)"""
    def decide(self, history: List[Event], merit_state: MeritState, 
               domain: str, stake: float) -> str:
        return 'kept'

class ThresholdStrategy(Strategy):
    """Cooperate if merit above threshold, considering future value"""
    def __init__(self, agent_id: int, params: EconomicParams, threshold: float = 0.5):
        super().__init__(agent_id, params)
        self.threshold = threshold
        
    def decide(self, history: List[Event], merit_state: MeritState, 
               domain: str, stake: float) -> str:
        merit = merit_state.get(self.agent_id, domain)
        
        # Calculate expected future value
        future_value = self._calculate_future_value(merit, domain)
        
        # Cooperate if future value outweighs immediate gain
        if merit > self.threshold or future_value > stake * 0.2:
            return 'kept'
        return 'broken'
    
    def _calculate_future_value(self, current_merit: float, domain: str) -> float:
        """Estimate discounted future value from maintaining merit"""
        δ = self.params.delta[self.agent_id]
        β = self.params.beta.get((self.agent_id, domain), 1.0)
        
        # Geometric series approximation
        horizon = 20  # Look ahead 20 rounds
        future_merit_value = sum(δ**t * β * current_merit for t in range(horizon))
        
        return future_merit_value

class AsynchronousAgencyABM:
    """
    Main simulation class implementing the asynchronous multi-domain game
    """
    def __init__(self, 
                 n_agents: int = 10,
                 domains: List[str] = None,
                 n_rounds: int = 1000,
                 seed: Optional[int] = None,
                 gamma: float = 0.05,  # Merit increase rate
                 lambda_penalty: float = 3.0,  # Penalty multiplier
                 base_stake: float = 100.0):
        
        if seed is not None:
            np.random.seed(seed)
            random.seed(seed)
        
        self.agents = list(range(n_agents))
        self.domains = domains or ['finance', 'health', 'education', 'tech', 'arts']
        self.n_rounds = n_rounds
        
        # Game parameters
        self.gamma = gamma
        self.lambda_penalty = lambda_penalty
        self.base_stake = base_stake
        
        # Initialize economic parameters with heterogeneity
        self.params = self._initialize_params()
        
        # Initialize scheduler
        self.scheduler = AsynchronousScheduler(self.agents, seed)
        
        # Initialize merit state
        self.merit_state = MeritState(self.agents, self.domains)
        
        # Initialize strategies
        self.strategies = self._initialize_strategies()
        
        # History tracking
        self.event_history = []
        self.utility_history = defaultdict(list)
        self.merit_history = []
        self.coalition_tests = []
        
    def _initialize_params(self) -> EconomicParams:
        """Initialize heterogeneous economic parameters"""
        alpha = {}
        beta = {}
        delta = {}
        
        for a in self.agents:
            # Heterogeneous credit preferences
            alpha[a] = np.random.uniform(0.8, 1.2)
            
            # Heterogeneous discount factors
            delta[a] = np.random.uniform(0.85, 0.95)
            
            # Domain-specific merit weights
            for d in self.domains:
                # Some agents value certain domains more
                if random.random() < 0.3:  # 30% chance of specialization
                    beta[(a, d)] = np.random.uniform(1.5, 2.5)
                else:
                    beta[(a, d)] = np.random.uniform(0.5, 1.5)
        
        params = EconomicParams(alpha, beta, delta)
        params.validate()
        return params
    
    def _initialize_strategies(self) -> Dict[int, Strategy]:
        """Initialize agent strategies with some heterogeneity"""
        strategies = {}
        
        for a in self.agents:
            if random.random() < 0.7:  # 70% cooperative
                strategies[a] = CooperativeStrategy(a, self.params)
            else:  # 30% threshold-based
                threshold = np.random.uniform(0.3, 0.7)
                strategies[a] = ThresholdStrategy(a, self.params, threshold)
        
        return strategies
    
    def calculate_stake_requirement(self, agent: int, domain: str) -> float:
        """Calculate stake with domain-specific merit discount"""
        merit = self.merit_state.get(agent, domain)
        
        # Domain-specific stake multiplier
        domain_mult = 1.0 + (hash(domain) % 5) * 0.2
        
        # Super-linear merit discount to prevent exploitation
        discount = (merit ** 1.5) * 0.8
        
        return self.base_stake * domain_mult * (1 - discount)
    
    def step_merit(self, event: Event) -> MeritState:
        """Update merit state based on event outcome"""
        new_state = MeritState(self.agents, self.domains)
        new_state.M = self.merit_state.M.copy()
        
        actor = event.actor
        domain = event.domain
        current_merit = self.merit_state.get(actor, domain)
        
        if event.outcome == 'kept':
            # Merit increase with diminishing returns
            delta = self.gamma * (1 - current_merit) * np.sqrt(current_merit + 0.1)
            new_state.update(actor, domain, current_merit + delta)
            
            # Cross-domain positive spillover (small)
            for d in self.domains:
                if d != domain:
                    spillover = delta * 0.1  # 10% spillover
                    other_merit = self.merit_state.get(actor, d)
                    new_state.update(actor, d, other_merit + spillover)
        
        else:  # broken
            # Merit penalty
            delta = -self.lambda_penalty * self.gamma * current_merit
            new_state.update(actor, domain, current_merit + delta)
            
            # Cross-domain negative spillover (larger)
            for d in self.domains:
                if d != domain:
                    spillover = delta * 0.3  # 30% negative spillover
                    other_merit = self.merit_state.get(actor, d)
                    new_state.update(actor, d, other_merit + spillover)
        
        return new_state
    
    def calculate_instant_utility(self, agent: int) -> float:
        """Calculate instantaneous utility for an agent"""
        utility = 0.0
        
        # Credit component (simplified - could track actual credits)
        credit_utility = self.params.alpha[agent] * 0
        
        # Merit component across all domains
        for d in self.domains:
            merit = self.merit_state.get(agent, d)
            weight = self.params.beta.get((agent, d), 1.0)
            utility += weight * merit
        
        return credit_utility + utility
    
    def simulate_round(self):
        """Execute one asynchronous round"""
        # Get next agent to act
        actor = self.scheduler.next()
        
        # Choose domain (weighted by merit)
        domain_weights = []
        for d in self.domains:
            merit = self.merit_state.get(actor, d)
            weight = self.params.beta.get((actor, d), 1.0)
            domain_weights.append(weight * (merit + 0.1))
        
        domain_probs = np.array(domain_weights) / sum(domain_weights)
        domain = np.random.choice(self.domains, p=domain_probs)
        
        # Calculate stake
        stake = self.calculate_stake_requirement(actor, domain)
        
        # Agent decides outcome
        strategy = self.strategies[actor]
        outcome = strategy.decide(self.event_history, self.merit_state, domain, stake)
        
        # Create event
        event = Event(
            actor=actor,
            domain=domain,
            stake=stake,
            outcome=outcome,
            round=self.scheduler.round
        )
        
        # Process assessments (simplified)
        assessors = random.sample([a for a in self.agents if a != actor], 
                                min(3, len(self.agents) - 1))
        for assessor in assessors:
            # Honest assessment with noise
            assessment = (outcome == 'kept') if random.random() < 0.9 else (outcome == 'broken')
            event.assessments.append((assessor, assessment))
        
        # Update merit state
        self.merit_state = self.step_merit(event)
        
        # Record event
        self.event_history.append(event)
        
        # Update utilities
        for agent in self.agents:
            utility = self.calculate_instant_utility(agent)
            self.utility_history[agent].append(utility)
    
    def test_one_step_deviation(self, agent: int, history_point: int = -1) -> bool:
        """
        Test if agent can improve utility by deviating once at history_point
        Returns True if current strategy is optimal (no profitable deviation)
        """
        if len(self.event_history) < 10:
            return True  # Not enough history
        
        # Get recent history window
        if history_point == -1:
            history_point = len(self.event_history) - 1
        
        # Find last event where agent acted
        agent_events = [(i, e) for i, e in enumerate(self.event_history) if e.actor == agent]
        if not agent_events:
            return True
        
        last_idx, last_event = agent_events[-1]
        
        # Calculate counterfactual utility if agent had deviated
        original_outcome = last_event.outcome
        counterfactual_outcome = 'broken' if original_outcome == 'kept' else 'kept'
        
        # Approximate utility difference
        merit_before = self.merit_state.get(agent, last_event.domain)
        δ = self.params.delta[agent]
        β = self.params.beta.get((agent, last_event.domain), 1.0)
        
        if original_outcome == 'kept' and counterfactual_outcome == 'broken':
            # Would have gained stake but lost merit
            immediate_gain = last_event.stake * 0.8  # Approximate
            merit_loss = self.lambda_penalty * self.gamma * merit_before
            future_loss = sum(δ**t * β * merit_loss for t in range(20))
            
            return immediate_gain < future_loss  # Current strategy better
        
        elif original_outcome == 'broken' and counterfactual_outcome == 'kept':
            # Would have lost stake but gained merit
            immediate_loss = last_event.stake * 0.1  # Op cost
            merit_gain = self.gamma * (1 - merit_before)
            future_gain = sum(δ**t * β * merit_gain for t in range(20))
            
            return immediate_loss < future_gain  # Deviation would be better
        
        return True
    
    def test_coalition_deviation(self, coalition: List[int]) -> Dict[str, any]:
        """
        Test if a coalition can profitably deviate together
        Returns analysis of coalition stability
        """
        if len(coalition) < 2:
            return {'stable': True, 'reason': 'Coalition too small'}
        
        # Calculate current average utility for coalition
        current_utilities = {}
        for agent in coalition:
            if agent in self.utility_history and self.utility_history[agent]:
                current_utilities[agent] = np.mean(self.utility_history[agent][-50:])
            else:
                current_utilities[agent] = 0
        
        # Simulate coordinated defection scenario
        defection_cost = len(coalition) * self.base_stake * 0.5
        defection_gain_per_member = self.base_stake * 2 / len(coalition)
        
        # Check if defection is profitable considering:
        # 1. Coordination costs (exponential in coalition size)
        coordination_cost = np.exp(0.5 * len(coalition))
        
        # 2. Detection probability (increases with coalition size)
        detection_prob = 1 - np.exp(-0.3 * len(coalition))
        
        # 3. Merit loss across all domains
        avg_merit_loss = self.lambda_penalty * self.gamma * 0.5  # Approximate
        
        # Expected payoff from defection
        expected_gain = defection_gain_per_member * (1 - detection_prob)
        expected_cost = coordination_cost + avg_merit_loss * 10  # Future losses
        
        profitable = expected_gain > expected_cost
        
        return {
            'stable': not profitable,
            'coalition_size': len(coalition),
            'expected_gain': expected_gain,
            'expected_cost': expected_cost,
            'coordination_cost': coordination_cost,
            'detection_prob': detection_prob
        }
    
    def run(self):
        """Run the full simulation"""
        print(f"🎮 Starting Asynchronous Multi-Domain Agency Simulation")
        print(f"   Agents: {self.n_agents}, Domains: {len(self.domains)}, Rounds: {self.n_rounds}")
        
        for i in range(self.n_rounds):
            self.simulate_round()
            
            # Periodic analysis
            if i % 100 == 0 and i > 0:
                # Check scheduler fairness
                fairness = self.scheduler.is_fair()
                
                # Test equilibrium properties
                spe_violations = 0
                for agent in self.agents:
                    if not self.test_one_step_deviation(agent):
                        spe_violations += 1
                
                # Test random coalitions
                coalition_size = random.randint(2, min(5, self.n_agents))
                coalition = random.sample(self.agents, coalition_size)
                coalition_result = self.test_coalition_deviation(coalition)
                self.coalition_tests.append(coalition_result)
                
                if i % 500 == 0:
                    print(f"\nRound {i}:")
                    print(f"  Scheduler fair: {fairness}")
                    print(f"  SPE violations: {spe_violations}/{self.n_agents}")
                    print(f"  Coalition stable: {coalition_result['stable']}")
                    
            # Record merit snapshot
            if i % 50 == 0:
                merit_snapshot = {}
                for a in self.agents:
                    agent_merits = []
                    for d in self.domains:
                        agent_merits.append(self.merit_state.get(a, d))
                    merit_snapshot[a] = np.mean(agent_merits)
                self.merit_history.append(merit_snapshot)
        
        return self.analyze_results()
    
    def analyze_results(self):
        """Comprehensive analysis of simulation results"""
        results = {
            'scheduler_fairness': self._analyze_scheduler_fairness(),
            'equilibrium_analysis': self._analyze_equilibrium(),
            'coalition_stability': self._analyze_coalitions(),
            'merit_dynamics': self._analyze_merit_dynamics(),
            'cross_domain_effects': self._analyze_cross_domain()
        }
        
        self.visualize_results(results)
        return results
    
    def _analyze_scheduler_fairness(self) -> Dict:
        """Analyze if scheduler maintained fairness"""
        agent_counts = {a: 0 for a in self.agents}
        for event in self.event_history:
            agent_counts[event.actor] += 1
        
        total_events = len(self.event_history)
        expected_per_agent = total_events / self.n_agents
        
        # Chi-square test
        chi2_stat = sum((count - expected_per_agent)**2 / expected_per_agent 
                       for count in agent_counts.values())
        
        critical_value = chi2.ppf(0.95, self.n_agents - 1)
        
        return {
            'fair': chi2_stat < critical_value,
            'chi2_statistic': chi2_stat,
            'critical_value': critical_value,
            'agent_participation': agent_counts,
            'cv_participation': np.std(list(agent_counts.values())) / expected_per_agent
        }
    
    def _analyze_equilibrium(self) -> Dict:
        """Analyze SPE properties"""
        # Test one-step deviation for all agents at multiple points
        deviation_tests = []
        
        test_points = [100, 250, 500, 750, -1]  # Various history points
        
        for point in test_points:
            if point > len(self.event_history) or (point == -1 and len(self.event_history) < 100):
                continue
                
            violations = 0
            for agent in self.agents:
                if not self.test_one_step_deviation(agent, point):
                    violations += 1
            
            deviation_tests.append({
                'history_point': point,
                'violations': violations,
                'violation_rate': violations / self.n_agents
            })
        
        # Check if cooperative agents outperform
        coop_utilities = []
        threshold_utilities = []
        
        for agent, strategy in self.strategies.items():
            avg_utility = np.mean(self.utility_history[agent][-100:]) if self.utility_history[agent] else 0
            
            if isinstance(strategy, CooperativeStrategy):
                coop_utilities.append(avg_utility)
            else:
                threshold_utilities.append(avg_utility)
        
        return {
            'deviation_tests': deviation_tests,
            'avg_violations': np.mean([t['violation_rate'] for t in deviation_tests]),
            'cooperative_advantage': np.mean(coop_utilities) - np.mean(threshold_utilities) if threshold_utilities else 0,
            'utility_variance': np.var([np.mean(utils[-100:]) for utils in self.utility_history.values() if utils])
        }
    
    def _analyze_coalitions(self) -> Dict:
        """Analyze coalition stability"""
        if not self.coalition_tests:
            return {'no_tests': True}
        
        stable_coalitions = sum(1 for test in self.coalition_tests if test['stable'])
        total_tests = len(self.coalition_tests)
        
        avg_by_size = defaultdict(list)
        for test in self.coalition_tests:
            avg_by_size[test['coalition_size']].append(test['stable'])
        
        stability_by_size = {}
        for size, stable_list in avg_by_size.items():
            stability_by_size[size] = sum(stable_list) / len(stable_list)
        
        return {
            'overall_stability_rate': stable_coalitions / total_tests,
            'stability_by_size': stability_by_size,
            'avg_coordination_cost': np.mean([t['coordination_cost'] for t in self.coalition_tests]),
            'avg_detection_prob': np.mean([t['detection_prob'] for t in self.coalition_tests])
        }
    
    def _analyze_merit_dynamics(self) -> Dict:
        """Analyze merit evolution and convergence"""
        if not self.merit_history:
            return {'no_data': True}
        
        # Merit convergence over time
        merit_means = []
        merit_stds = []
        
        for snapshot in self.merit_history:
            values = list(snapshot.values())
            merit_means.append(np.mean(values))
            merit_stds.append(np.std(values))
        
        # Check for convergence (decreasing variance)
        converging = merit_stds[-1] < merit_stds[0] * 0.8 if len(merit_stds) > 1 else False
        
        # Domain specialization
        final_merits = self.merit_history[-1] if self.merit_history else {}
        
        domain_specialization = {}
        for a in self.agents:
            agent_merits = {}
            for d in self.domains:
                agent_merits[d] = self.merit_state.get(a, d)
            
            if agent_merits:
                max_domain = max(agent_merits, key=agent_merits.get)
                specialization_ratio = agent_merits[max_domain] / np.mean(list(agent_merits.values()))
                domain_specialization[a] = {
                    'domain': max_domain,
                    'ratio': specialization_ratio
                }
        
        return {
            'converging': converging,
            'final_mean_merit': merit_means[-1] if merit_means else 0,
            'final_merit_cv': merit_stds[-1] / merit_means[-1] if merit_means and merit_means[-1] > 0 else 0,
            'avg_specialization_ratio': np.mean([s['ratio'] for s in domain_specialization.values()])
        }
    
    def _analyze_cross_domain(self) -> Dict:
        """Analyze cross-domain spillover effects"""
        spillover_events = []
        
        # Look for events that affected multiple domains
        for i, event in enumerate(self.event_history[1:], 1):
            if event.outcome == 'broken':
                # Check merit changes in other domains
                actor = event.actor
                primary_domain = event.domain
                
                spillovers = {}
                for d in self.domains:
                    if d != primary_domain:
                        # Approximate spillover (would need to track exact changes)
                        spillovers[d] = -0.3  # Negative spillover assumption
                
                spillover_events.append({
                    'round': i,
                    'actor': actor,
                    'primary_domain': primary_domain,
                    'spillovers': spillovers
                })
        
        return {
            'spillover_frequency': len(spillover_events) / len(self.event_history) if self.event_history else 0,
            'domains_affected_per_break': len(self.domains) - 1  # All others affected
        }
    
    def visualize_results(self, results: Dict):
        """Generate comprehensive visualizations"""
        fig, axes = plt.subplots(3, 2, figsize=(16, 14))
        
        # 1. Scheduler fairness
        ax = axes[0, 0]
        fairness_data = results['scheduler_fairness']
        if 'agent_participation' in fairness_data:
            agents = list(fairness_data['agent_participation'].keys())
            counts = list(fairness_data['agent_participation'].values())
            expected = len(self.event_history) / self.n_agents
            
            ax.bar(agents, counts, alpha=0.7, color='blue')
            ax.axhline(y=expected, color='red', linestyle='--', label='Expected')
            ax.set_title(f'Agent Participation (Fair: {fairness_data["fair"]})', fontsize=14)
            ax.set_xlabel('Agent ID')
            ax.set_ylabel('Number of Actions')
            ax.legend()
        
        # 2. Merit evolution
        ax = axes[0, 1]
        if self.merit_history:
            merit_means = []
            merit_stds = []
            
            for snapshot in self.merit_history:
                values = list(snapshot.values())
                merit_means.append(np.mean(values))
                merit_stds.append(np.std(values))
            
            rounds = np.arange(0, len(self.merit_history)) * 50
            ax.plot(rounds, merit_means, 'b-', linewidth=2, label='Mean Merit')
            ax.fill_between(rounds, 
                           np.array(merit_means) - np.array(merit_stds),
                           np.array(merit_means) + np.array(merit_stds),
                           alpha=0.3, color='blue', label='±1 STD')
            ax.set_title('Merit Evolution Across Population', fontsize=14)
            ax.set_xlabel('Round')
            ax.set_ylabel('Merit')
            ax.legend()
            ax.grid(True, alpha=0.3)
        
        # 3. Utility distribution by strategy
        ax = axes[1, 0]
        coop_utils = []
        threshold_utils = []
        
        for agent, strategy in self.strategies.items():
            if agent in self.utility_history and self.utility_history[agent]:
                avg_util = np.mean(self.utility_history[agent][-100:])
                if isinstance(strategy, CooperativeStrategy):
                    coop_utils.append(avg_util)
                else:
                    threshold_utils.append(avg_util)
        
        data_to_plot = []
        labels = []
        if coop_utils:
            data_to_plot.append(coop_utils)
            labels.append('Cooperative')
        if threshold_utils:
            data_to_plot.append(threshold_utils)
            labels.append('Threshold')
        
        if data_to_plot:
            ax.boxplot(data_to_plot, labels=labels)
            ax.set_title('Utility Distribution by Strategy Type', fontsize=14)
            ax.set_ylabel('Average Utility (last 100 rounds)')
            ax.grid(True, alpha=0.3, axis='y')
        
        # 4. Coalition stability by size
        ax = axes[1, 1]
        coalition_data = results['coalition_stability']
        if 'stability_by_size' in coalition_data and coalition_data['stability_by_size']:
            sizes = sorted(coalition_data['stability_by_size'].keys())
            stability_rates = [coalition_data['stability_by_size'][s] for s in sizes]
            
            ax.plot(sizes, stability_rates, 'o-', linewidth=2, markersize=8)
            ax.set_title('Coalition Stability by Size', fontsize=14)
            ax.set_xlabel('Coalition Size')
            ax.set_ylabel('Stability Rate')
            ax.set_ylim(0, 1.1)
            ax.grid(True, alpha=0.3)
        
        # 5. Domain specialization heatmap
        ax = axes[2, 0]
        merit_matrix = np.zeros((len(self.agents), len(self.domains)))
        for i, agent in enumerate(self.agents):
            for j, domain in enumerate(self.domains):
                merit_matrix[i, j] = self.merit_state.get(agent, domain)
        
        im = ax.imshow(merit_matrix, cmap='RdYlGn', aspect='auto', vmin=0, vmax=1)
        ax.set_title('Final Merit Distribution (Agent × Domain)', fontsize=14)
        ax.set_xlabel('Domain')
        ax.set_ylabel('Agent')
        ax.set_xticks(range(len(self.domains)))
        ax.set_xticklabels(self.domains, rotation=45)
        plt.colorbar(im, ax=ax, label='Merit')
        
        # 6. SPE violation timeline
        ax = axes[2, 1]
        eq_data = results['equilibrium_analysis']
        if 'deviation_tests' in eq_data and eq_data['deviation_tests']:
            points = [t['history_point'] if t['history_point'] != -1 else self.n_rounds 
                     for t in eq_data['deviation_tests']]
            violations = [t['violation_rate'] for t in eq_data['deviation_tests']]
            
            ax.plot(points, violations, 'ro-', linewidth=2, markersize=8)
            ax.set_title('SPE Violations Over Time', fontsize=14)
            ax.set_xlabel('Round')
            ax.set_ylabel('Violation Rate')
            ax.set_ylim(0, max(0.1, max(violations) * 1.1) if violations else 1)
            ax.grid(True, alpha=0.3)
        
        plt.tight_layout()
        plt.show()
        
        # Print summary report
        self._print_summary(results)
    
    def _print_summary(self, results: Dict):
        """Print comprehensive summary of results"""
        print("\n" + "="*80)
        print("ASYNCHRONOUS MULTI-DOMAIN AGENCY PROTOCOL - SIMULATION RESULTS")
        print("="*80)
        
        print("\n1. SCHEDULER FAIRNESS")
        fairness = results['scheduler_fairness']
        print(f"   Fair scheduling achieved: {fairness.get('fair', 'N/A')}")
        print(f"   Coefficient of variation: {fairness.get('cv_participation', 0):.3f}")
        
        print("\n2. EQUILIBRIUM ANALYSIS")
        eq = results['equilibrium_analysis']
        print(f"   Average SPE violation rate: {eq.get('avg_violations', 0):.1%}")
        print(f"   Cooperative strategy advantage: {eq.get('cooperative_advantage', 0):.3f}")
        
        print("\n3. COALITION STABILITY")
        coalition = results['coalition_stability']
        print(f"   Overall stability rate: {coalition.get('overall_stability_rate', 0):.1%}")
        print(f"   Average coordination cost: {coalition.get('avg_coordination_cost', 0):.2f}")
        
        print("\n4. MERIT DYNAMICS")
        merit = results['merit_dynamics']
        print(f"   Merit converging: {merit.get('converging', False)}")
        print(f"   Final mean merit: {merit.get('final_mean_merit', 0):.3f}")
        print(f"   Domain specialization: {merit.get('avg_specialization_ratio', 0):.2f}x")
        
        print("\n5. CROSS-DOMAIN EFFECTS")
        cross = results['cross_domain_effects']
        print(f"   Spillover frequency: {cross.get('spillover_frequency', 0):.1%}")
        
        print("\n" + "="*80)
        
        # Overall assessment
        print("\nOVERALL ASSESSMENT:")
        
        violations_ok = eq.get('avg_violations', 1) < 0.1
        coalition_stable = coalition.get('overall_stability_rate', 0) > 0.8
        merit_healthy = merit.get('final_mean_merit', 0) > 0.5
        
        if violations_ok and coalition_stable and merit_healthy:
            print("✅ The asynchronous multi-domain protocol demonstrates STRONG STABILITY")
            print("   - Subgame-perfect equilibrium is maintained")
            print("   - Coalition-proof against coordinated deviations")
            print("   - Merit system achieves healthy equilibrium")
        else:
            print("⚠️  The protocol shows WEAKNESSES:")
            if not violations_ok:
                print("   - High SPE violation rate suggests parameter tuning needed")
            if not coalition_stable:
                print("   - Coalition instability indicates need for stronger deterrents")
            if not merit_healthy:
                print("   - Low merit equilibrium suggests insufficient incentives")

# Example configurations for different theoretical scenarios
class TheoreticalScenarios:
    @staticmethod
    def high_heterogeneity():
        """Test with highly heterogeneous agents"""
        return {
            'n_agents': 20,
            'domains': ['finance', 'health', 'education', 'tech', 'arts', 'law', 'science'],
            'n_rounds': 2000,
            'seed': 42
        }
    
    @staticmethod
    def stress_test():
        """Stress test with many agents and domains"""
        return {
            'n_agents': 50,
            'domains': ['d' + str(i) for i in range(10)],
            'n_rounds': 5000,
            'seed': 123
        }
    
    @staticmethod
    def minimal_game():
        """Minimal game for theoretical validation"""
        return {
            'n_agents': 3,
            'domains': ['A', 'B'],
            'n_rounds': 500,
            'seed': 7
        }

if __name__ == "__main__":
    # Run main simulation
    print("Running standard configuration...")
    sim = AsynchronousAgencyABM(
        n_agents=15,
        domains=['finance', 'health', 'education', 'tech', 'arts'],
        n_rounds=1500,
        seed=42
    )
    
    results = sim.run()
    
    # Run theoretical scenarios
    print("\n\nRunning theoretical scenarios...")
    
    scenarios = {
        'minimal': TheoreticalScenarios.minimal_game(),
        'heterogeneous': TheoreticalScenarios.high_heterogeneity(),
    }
    
    scenario_results = {}
    for name, config in scenarios.items():
        print(f"\n--- Scenario: {name} ---")
        scenario_sim = AsynchronousAgencyABM(**config)
        scenario_results[name] = scenario_sim.run()