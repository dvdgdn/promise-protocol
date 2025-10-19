import numpy as np
import matplotlib.pyplot as plt
from dataclasses import dataclass, field
from typing import Dict, List, Any, Optional, Tuple
from collections import defaultdict, deque
import pandas as pd
import random

@dataclass
class Promise:
    """Represents a promise made by an agent."""
    promiser_id: int
    domain: str
    stake: float
    value: float
    is_high_value: bool = False
    actual_outcome: Optional[bool] = None
    round_number: int = 0

class Agent:
    """Base class for an agent in the protocol."""
    def __init__(self, agent_id: int, initial_credits: float, domains: List[str]):
        self.id = agent_id
        self.credits = initial_credits
        self.initial_credits = initial_credits
        self.merit = {domain: np.random.uniform(0.1, 0.3) for domain in domains}
        self.merit_history = defaultdict(list)  # Track merit changes
        self.type = "Honest"
        self.state = "normal"  # normal, cooldown, attacking
        self.cooldown_remaining = 0
        self.promises_made = []
        self.promises_broken = []
        
    def get_merit(self, domain: str) -> float:
        return self.merit.get(domain, 0.1)
    
    def update_merit(self, domain: str, delta: float):
        current = self.get_merit(domain)
        new_merit = max(0.0, min(1.0, current + delta))
        self.merit[domain] = new_merit
        self.merit_history[domain].append((self.merit[domain], delta))
    
    def get_merit_velocity(self, domain: str, window: int = 5) -> float:
        """Calculate recent merit change velocity"""
        history = self.merit_history[domain]
        if len(history) < 2:
            return 0.0
        
        recent = history[-window:]
        if len(recent) < 2:
            return 0.0
            
        total_change = sum(delta for _, delta in recent)
        return total_change / len(recent)
    
    def decide_on_promise(self, promise_details: Dict[str, Any]) -> bool:
        """Default honest agent always keeps promises."""
        return True

class BurstAttackAgent(Agent):
    """Agent that launches coordinated burst attacks after patience period."""
    def __init__(self, agent_id: int, initial_credits: float, domains: List[str], 
                 patience_rounds: int, burst_duration: int = 5):
        super().__init__(agent_id, initial_credits, domains)
        self.type = "BurstAttacker"
        self.patience_rounds = patience_rounds
        self.burst_duration = burst_duration
        self.burst_remaining = 0
        self.attacks_launched = 0
        
    def decide_on_promise(self, promise_details: Dict[str, Any]) -> bool:
        current_round = promise_details["current_round"]
        
        # Wait for patience period
        if current_round < self.patience_rounds:
            return True  # Build merit honestly
        
        # Start burst attack
        if self.burst_remaining == 0 and self.attacks_launched == 0:
            self.burst_remaining = self.burst_duration
            self.state = "attacking"
            self.attacks_launched += 1
        
        # During burst attack
        if self.burst_remaining > 0:
            self.burst_remaining -= 1
            return False  # Break promise
            
        # After burst, return to normal
        self.state = "normal"
        return True

class SleeperAgent(Agent):
    """An agent that behaves honestly to build merit, then defects."""
    def __init__(self, agent_id: int, initial_credits: float, domains: List[str], 
                 defect_round: int):
        super().__init__(agent_id, initial_credits, domains)
        self.defect_round = defect_round
        self.type = "Sleeper"
        self.has_defected = False
        
    def decide_on_promise(self, promise_details: Dict[str, Any]) -> bool:
        current_round = promise_details["current_round"]
        is_high_value = promise_details["is_high_value"]
        
        if current_round >= self.defect_round and is_high_value and not self.has_defected:
            self.has_defected = True
            self.state = "attacking"
            return False
        return True

class AdaptiveLearningAgent(Agent):
    """Agent that uses advanced learning to adapt strategy."""
    def __init__(self, agent_id: int, initial_credits: float, domains: List[str]):
        super().__init__(agent_id, initial_credits, domains)
        self.type = "AdaptiveLearning"
        self.strategy_history = deque(maxlen=50)  # Remember recent strategies
        self.observed_outcomes = defaultdict(list)  # Track neighbor outcomes
        self.honesty_rate = 0.7  # Start somewhat honest
        self.exploitation_memory = {}  # Remember successful exploits
        
    def decide_on_promise(self, promise_details: Dict[str, Any]) -> bool:
        domain = promise_details["domain"]
        stake = promise_details["stake"]
        value = promise_details["value"]
        
        # Check if we've found a profitable exploit pattern
        exploit_key = (domain, value > 500)  # High value promises
        if exploit_key in self.exploitation_memory:
            past_success = self.exploitation_memory[exploit_key]
            if past_success > 0.3:  # Exploit worked before
                return False
        
        # Otherwise use adaptive honesty rate
        decision = np.random.random() < self.honesty_rate
        self.strategy_history.append((decision, domain, stake, value))
        return decision
    
    def update_strategy(self, neighbors: List[Agent], network_state: Dict):
        """Advanced strategy update based on multiple signals."""
        if not neighbors:
            return
        
        # 1. Analyze neighbor performance
        neighbor_performance = []
        for n in neighbors:
            profit_rate = (n.credits - n.initial_credits) / n.initial_credits
            avg_merit = np.mean(list(n.merit.values()))
            neighbor_performance.append({
                'agent': n,
                'profit_rate': profit_rate,
                'avg_merit': avg_merit,
                'type': n.type
            })
        
        # 2. Find best performing strategy
        best_performer = max(neighbor_performance, key=lambda x: x['profit_rate'])
        
        # 3. Detect if dishonesty is profitable
        dishonest_profitable = False
        for perf in neighbor_performance:
            if perf['agent'].type in ['BurstAttacker', 'Sleeper'] and perf['profit_rate'] > 0.1:
                dishonest_profitable = True
                break
        
        # 4. Update exploitation memory
        for decision, domain, stake, value in self.strategy_history:
            exploit_key = (domain, value > 500)
            if not decision:  # We broke promise
                outcome = self.credits > self.initial_credits
                if exploit_key not in self.exploitation_memory:
                    self.exploitation_memory[exploit_key] = []
                self.exploitation_memory[exploit_key].append(1 if outcome else 0)
        
        # Clean exploitation memory
        for key in list(self.exploitation_memory.keys()):
            if len(self.exploitation_memory[key]) > 10:
                self.exploitation_memory[key] = np.mean(self.exploitation_memory[key][-10:])
        
        # 5. Adapt honesty rate
        if dishonest_profitable:
            # Network is vulnerable, become more dishonest
            self.honesty_rate *= 0.9
        else:
            # Honesty pays, increase honesty
            target_honesty = 0.95 if best_performer['type'] == 'Honest' else 0.7
            self.honesty_rate += 0.1 * (target_honesty - self.honesty_rate)
        
        self.honesty_rate = max(0.1, min(0.95, self.honesty_rate))

class HonestAgent(Agent):
    """A consistently honest agent."""
    def __init__(self, agent_id: int, initial_credits: float, domains: List[str]):
        super().__init__(agent_id, initial_credits, domains)
        self.type = "Honest"

class ImprovedAdvancedAdversarySimulation:
    """Enhanced simulation with merit velocity and sophisticated attacks."""
    def __init__(self, n_agents=100, n_rounds=300, seed: Optional[int] = None,
                 n_honest=50, n_sleeper=15, n_burst=15, n_learning=20,
                 merit_velocity_threshold=-0.25, cooldown_rounds=10):
        
        if seed is not None:
            np.random.seed(seed)
            random.seed(seed)
            
        self.n_agents = n_agents
        self.n_rounds = n_rounds
        self.domains = [f"domain_{i}" for i in range(5)]
        
        # Economic parameters
        self.base_stake = 100.0
        self.op_cost_percentage = 0.05
        self.lambda_penalty = 3.0  # Higher penalty
        self.gamma = 0.02  # Merit change rate
        
        # Merit velocity defense
        self.merit_velocity_threshold = merit_velocity_threshold
        self.cooldown_rounds = cooldown_rounds
        
        # Agent populations
        self.agents = self._initialize_agents(n_honest, n_sleeper, n_burst, n_learning)
        self.round_num = 0
        
        # History tracking
        self.agent_history = defaultdict(lambda: {
            'credits': [], 'avg_merit': [], 'state': [], 'promises_kept': 0, 
            'promises_broken': 0, 'cooldown_triggers': 0
        })
        self.network_history = {
            'total_promises': [],
            'broken_promises': [],
            'cooldown_agents': [],
            'attack_events': []
        }
        
    def _initialize_agents(self, n_honest, n_sleeper, n_burst, n_learning):
        agents = {}
        agent_id = 0
        initial_credits = 1000.0
        
        # Honest agents
        for _ in range(n_honest):
            agents[agent_id] = HonestAgent(agent_id, initial_credits, self.domains)
            agent_id += 1
        
        # Sleeper agents
        for _ in range(n_sleeper):
            defect_round = np.random.randint(self.n_rounds // 2, int(self.n_rounds * 0.8))
            agents[agent_id] = SleeperAgent(agent_id, initial_credits, self.domains, defect_round)
            agent_id += 1
        
        # Burst attack agents
        for _ in range(n_burst):
            patience = np.random.randint(20, 80)
            burst_duration = np.random.randint(3, 8)
            agents[agent_id] = BurstAttackAgent(agent_id, initial_credits, self.domains, 
                                              patience, burst_duration)
            agent_id += 1
        
        # Adaptive learning agents
        for _ in range(n_learning):
            agents[agent_id] = AdaptiveLearningAgent(agent_id, initial_credits, self.domains)
            agent_id += 1
            
        return agents
    
    def check_merit_velocity_defense(self, agent: Agent, domain: str):
        """Check if agent triggered merit velocity defense."""
        velocity = agent.get_merit_velocity(domain)
        
        if velocity < self.merit_velocity_threshold and agent.state != 'cooldown':
            # Trigger cooldown
            agent.state = 'cooldown'
            agent.cooldown_remaining = self.cooldown_rounds
            self.agent_history[agent.id]['cooldown_triggers'] += 1
            
            # Log the event
            self.network_history['attack_events'].append({
                'round': self.round_num,
                'agent_id': agent.id,
                'agent_type': agent.type,
                'merit_drop': velocity,
                'domain': domain
            })
            
            print(f"⚠️  Round {self.round_num}: Agent {agent.id} ({agent.type}) "
                  f"triggered cooldown! Merit velocity: {velocity:.3f}")
    
    def simulate_round(self):
        self.round_num += 1
        round_promises = 0
        round_broken = 0
        
        # Update cooldowns
        for agent in self.agents.values():
            if agent.state == 'cooldown':
                agent.cooldown_remaining -= 1
                if agent.cooldown_remaining <= 0:
                    agent.state = 'normal'
        
        # Agents make promises
        for agent in self.agents.values():
            if agent.credits < self.base_stake * 2:
                continue
            
            domain = random.choice(self.domains)
            merit = agent.get_merit(domain)
            
            # High value promises
            is_high_value = np.random.random() < 0.05
            promise_value = np.random.gamma(2, 100) * (5 if is_high_value else 1)
            
            # Calculate stake (no discount during cooldown)
            if agent.state == 'cooldown':
                stake = self.base_stake * (5 if is_high_value else 1)
            else:
                stake = self.base_stake * (5 if is_high_value else 1) * (1 - merit * 0.8)
            
            if agent.credits < stake:
                continue
            
            promise_details = {
                "current_round": self.round_num,
                "is_high_value": is_high_value,
                "domain": domain,
                "stake": stake,
                "value": promise_value
            }
            
            # Agent decides
            kept = agent.decide_on_promise(promise_details)
            agent.credits -= stake
            round_promises += 1
            
            # Create promise record
            promise = Promise(
                promiser_id=agent.id,
                domain=domain,
                stake=stake,
                value=promise_value,
                is_high_value=is_high_value,
                actual_outcome=kept,
                round_number=self.round_num
            )
            
            agent.promises_made.append(promise)
            if not kept:
                agent.promises_broken.append(promise)
                round_broken += 1
            
            # Process outcome
            op_cost = stake * self.op_cost_percentage
            
            if kept:
                # Promise kept
                agent.credits += (stake - op_cost)
                delta_merit = self.gamma * (1 - merit)
                agent.update_merit(domain, delta_merit)
                self.agent_history[agent.id]['promises_kept'] += 1
            else:
                # Promise broken
                delta_merit = -self.lambda_penalty * self.gamma * merit
                agent.update_merit(domain, delta_merit)
                self.agent_history[agent.id]['promises_broken'] += 1
                
                # Check for merit velocity trigger
                self.check_merit_velocity_defense(agent, domain)
        
        # Learning agents update strategy
        network_state = {
            'round': self.round_num,
            'total_promises': round_promises,
            'broken_ratio': round_broken / round_promises if round_promises > 0 else 0
        }
        
        for agent in self.agents.values():
            if isinstance(agent, AdaptiveLearningAgent):
                neighbors = random.sample(list(self.agents.values()), min(10, len(self.agents)-1))
                agent.update_strategy(neighbors, network_state)
        
        # Record network history
        self.network_history['total_promises'].append(round_promises)
        self.network_history['broken_promises'].append(round_broken)
        cooldown_count = sum(1 for a in self.agents.values() if a.state == 'cooldown')
        self.network_history['cooldown_agents'].append(cooldown_count)
        
        self._record_history()
    
    def _record_history(self):
        for agent_id, agent in self.agents.items():
            self.agent_history[agent_id]['credits'].append(agent.credits)
            avg_merit = np.mean(list(agent.merit.values()))
            self.agent_history[agent_id]['avg_merit'].append(avg_merit)
            self.agent_history[agent_id]['state'].append(agent.state)
            self.agent_history[agent_id]['type'] = agent.type
    
    def run(self):
        print("🚀 Starting Improved Advanced Adversary Simulation")
        
        for i in range(self.n_rounds):
            self.simulate_round()
            
            if i % 50 == 0:
                cooldowns = sum(1 for a in self.agents.values() if a.state == 'cooldown')
                broken_ratio = (self.network_history['broken_promises'][-1] / 
                              self.network_history['total_promises'][-1] 
                              if self.network_history['total_promises'][-1] > 0 else 0)
                
                print(f"Round {i}: Cooldowns={cooldowns}, "
                      f"Broken ratio={broken_ratio:.1%}")
        
        return self.agent_history, self.network_history
    
    def analyze_results(self):
        """Comprehensive analysis with visualizations."""
        fig, axes = plt.subplots(3, 2, figsize=(16, 14))
        
        # 1. Credits by agent type
        ax = axes[0, 0]
        for agent_type in ['Honest', 'Sleeper', 'BurstAttacker', 'AdaptiveLearning']:
            agent_ids = [i for i, data in self.agent_history.items() 
                        if data['type'] == agent_type]
            if not agent_ids:
                continue
            
            credits_history = np.array([self.agent_history[i]['credits'] for i in agent_ids])
            mean_credits = credits_history.mean(axis=0)
            ax.plot(mean_credits, label=f'{agent_type}', linewidth=2)
        
        ax.set_title('Average Credits by Agent Strategy', fontsize=14)
        ax.set_xlabel('Round')
        ax.set_ylabel('Average Credits')
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        # 2. Merit evolution with cooldown events
        ax = axes[0, 1]
        for agent_type in ['Honest', 'Sleeper', 'BurstAttacker']:
            agent_ids = [i for i, data in self.agent_history.items() 
                        if data['type'] == agent_type]
            if not agent_ids:
                continue
            
            merit_history = np.array([self.agent_history[i]['avg_merit'] for i in agent_ids])
            mean_merit = merit_history.mean(axis=0)
            ax.plot(mean_merit, label=f'{agent_type}', linewidth=2)
        
        # Mark cooldown events
        for event in self.network_history['attack_events']:
            ax.axvline(x=event['round'], color='red', alpha=0.3, linestyle='--')
        
        ax.set_title('Average Merit Evolution (red lines = cooldown triggers)', fontsize=14)
        ax.set_xlabel('Round')
        ax.set_ylabel('Average Merit')
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        # 3. Network health metrics
        ax = axes[1, 0]
        broken_ratio = np.array(self.network_history['broken_promises']) / np.maximum(
            np.array(self.network_history['total_promises']), 1)
        
        ax.plot(broken_ratio * 100, label='Broken Promises %', color='red', alpha=0.7)
        ax2 = ax.twinx()
        ax2.plot(self.network_history['cooldown_agents'], label='Cooldown Agents', 
                color='orange', alpha=0.7)
        
        ax.set_title('Network Health Indicators', fontsize=14)
        ax.set_xlabel('Round')
        ax.set_ylabel('Broken Promise %', color='red')
        ax2.set_ylabel('Agents in Cooldown', color='orange')
        ax.grid(True, alpha=0.3)
        
        # 4. Attack timeline
        ax = axes[1, 1]
        attack_data = pd.DataFrame(self.network_history['attack_events'])
        if not attack_data.empty:
            for agent_type in attack_data['agent_type'].unique():
                type_events = attack_data[attack_data['agent_type'] == agent_type]
                ax.scatter(type_events['round'], type_events['merit_drop'], 
                         label=agent_type, alpha=0.6, s=100)
            
            ax.axhline(y=self.merit_velocity_threshold, color='red', linestyle='--', 
                      label='Threshold')
            ax.set_title('Merit Velocity Attacks Detected', fontsize=14)
            ax.set_xlabel('Round')
            ax.set_ylabel('Merit Velocity (drop)')
            ax.legend()
        else:
            ax.text(0.5, 0.5, 'No attacks detected', transform=ax.transAxes, 
                   ha='center', va='center', fontsize=14)
            ax.set_title('Merit Velocity Attacks', fontsize=14)
        ax.grid(True, alpha=0.3)
        
        # 5. Final profitability scatter
        ax = axes[2, 0]
        final_data = []
        for agent_id, data in self.agent_history.items():
            agent = self.agents[agent_id]
            final_data.append({
                'type': data['type'],
                'credits': data['credits'][-1],
                'merit': data['avg_merit'][-1],
                'promises_broken': data['promises_broken'],
                'cooldown_triggers': data['cooldown_triggers']
            })
        
        plot_df = pd.DataFrame(final_data)
        colors = {'Honest': 'blue', 'Sleeper': 'red', 'BurstAttacker': 'orange', 
                 'AdaptiveLearning': 'green'}
        
        for agent_type, group in plot_df.groupby('type'):
            # Size by number of broken promises
            sizes = 50 + group['promises_broken'] * 10
            ax.scatter(group['credits'], group['merit'], alpha=0.6, 
                      label=agent_type, color=colors.get(agent_type, 'gray'),
                      s=sizes)
        
        ax.set_title('Final State (size = promises broken)', fontsize=14)
        ax.set_xlabel('Final Credits')
        ax.set_ylabel('Final Average Merit')
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        # 6. Strategy effectiveness
        ax = axes[2, 1]
        effectiveness = plot_df.groupby('type').agg({
            'credits': 'mean',
            'promises_broken': 'sum',
            'cooldown_triggers': 'sum'
        })
        
        x = np.arange(len(effectiveness))
        width = 0.25
        
        ax.bar(x - width, effectiveness['credits'], width, label='Avg Credits', alpha=0.7)
        ax.bar(x, effectiveness['promises_broken'] * 10, width, 
               label='Promises Broken x10', alpha=0.7)
        ax.bar(x + width, effectiveness['cooldown_triggers'] * 100, width, 
               label='Cooldowns x100', alpha=0.7)
        
        ax.set_title('Strategy Effectiveness Comparison', fontsize=14)
        ax.set_xlabel('Agent Type')
        ax.set_ylabel('Value')
        ax.set_xticks(x)
        ax.set_xticklabels(effectiveness.index, rotation=45)
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        plt.tight_layout()
        plt.show()
        
        # Print summary
        print("\n=== Simulation Summary ===")
        print(f"Total attack events detected: {len(self.network_history['attack_events'])}")
        
        profitability = plot_df.groupby('type')['credits'].mean().sort_values(ascending=False)
        print("\nAverage final credits by type:")
        for agent_type, avg_credits in profitability.items():
            print(f"  {agent_type}: {avg_credits:.0f}")
        
        print("\nMerit velocity defense effectiveness:")
        attack_df = pd.DataFrame(self.network_history['attack_events'])
        if not attack_df.empty:
            by_type = attack_df.groupby('agent_type').size()
            print("Cooldowns triggered by type:")
            for agent_type, count in by_type.items():
                print(f"  {agent_type}: {count}")
        
        # Check if defenses worked
        honest_profit = profitability.get('Honest', 0)
        attacker_profits = [profitability.get(t, 0) 
                           for t in ['Sleeper', 'BurstAttacker', 'AdaptiveLearning']]
        
        if all(honest_profit > ap for ap in attacker_profits):
            print("\n✅ SUCCESS: Honest agents outperformed all attack strategies!")
            print("   Merit velocity defense successfully deterred burst attacks.")
        else:
            print("\n⚠️  WARNING: Some attack strategies remain profitable!")
            print("   Consider increasing penalties or tightening velocity thresholds.")
        
        return plot_df, effectiveness

if __name__ == "__main__":
    # Run the improved simulation
    sim = ImprovedAdvancedAdversarySimulation(
        n_agents=120,
        n_rounds=300,
        seed=42,
        n_honest=60,
        n_sleeper=20,
        n_burst=20,
        n_learning=20,
        merit_velocity_threshold=-0.25,
        cooldown_rounds=15
    )
    
    agent_history, network_history = sim.run()
    final_stats, effectiveness = sim.analyze_results()