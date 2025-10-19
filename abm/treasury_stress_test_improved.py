import numpy as np
import matplotlib.pyplot as plt
from dataclasses import dataclass, field
from typing import Dict, List, Tuple, Optional
from collections import defaultdict
import pandas as pd
from scipy import stats
from scipy.stats import lognorm
import random

@dataclass
class Promise:
    """Represents a promise made by an agent"""
    promiser_id: int
    domain: str
    stake: float
    value: float
    actual_outcome: Optional[bool] = None

@dataclass
class Agent:
    """Represents an agent in the protocol"""
    id: int
    credits: float
    merit: Dict[str, float] = field(default_factory=dict)
    honesty_rate: float = 0.95

class TreasuryManagerAgent:
    """PID controller agent that manages treasury balance"""
    def __init__(self, 
                 target_buffer_months: float = 6.0,
                 kp: float = 0.01,  # Proportional gain
                 ki: float = 0.001,  # Integral gain
                 kd: float = 0.005,  # Derivative gain
                 min_op_cost: float = 0.01,
                 max_op_cost: float = 0.15):
        
        self.target_buffer_months = target_buffer_months
        self.kp = kp
        self.ki = ki
        self.kd = kd
        self.min_op_cost = min_op_cost
        self.max_op_cost = max_op_cost
        
        # PID state
        self.integral_error = 0.0
        self.last_error = 0.0
        self.avg_monthly_cost = 1000.0  # Initial estimate
        
    def update_op_cost(self, current_balance: float, recent_costs: List[float], 
                      current_op_cost: float) -> float:
        """Use PID control to adjust operational cost percentage"""
        # Update cost estimate
        if recent_costs:
            self.avg_monthly_cost = np.mean(recent_costs[-30:]) * 30  # 30 rounds = 1 month
        
        # Target balance
        target_balance = self.avg_monthly_cost * self.target_buffer_months
        
        # Calculate error
        error = (target_balance - current_balance) / target_balance
        
        # PID calculation
        proportional = self.kp * error
        self.integral_error += error
        integral = self.ki * self.integral_error
        derivative = self.kd * (error - self.last_error)
        
        # Update op_cost
        adjustment = proportional + integral + derivative
        new_op_cost = current_op_cost + adjustment
        
        # Clamp to valid range
        new_op_cost = max(self.min_op_cost, min(self.max_op_cost, new_op_cost))
        
        self.last_error = error
        
        return new_op_cost

class ImprovedTreasuryStressTestSimulation:
    """
    Enhanced treasury simulation with volatile costs and adaptive management
    """
    def __init__(self,
                 n_agents: int = 100,
                 n_rounds: int = 300,
                 base_stake: float = 100.0,
                 initial_op_cost_percentage: float = 0.05,
                 base_computation_cost: float = 150.0,
                 initial_credits: float = 1000.0,
                 initial_treasury: float = 20000.0,
                 seed: Optional[int] = None,
                 enable_adaptive_management: bool = True):

        # Set random seed
        if seed is not None:
            np.random.seed(seed)
            random.seed(seed)

        # Core parameters
        self.n_agents = n_agents
        self.n_rounds = n_rounds
        self.domains = [f"domain_{i}" for i in range(5)]
        
        # Economic model parameters
        self.base_stake = base_stake
        self.op_cost_percentage = initial_op_cost_percentage
        self.base_computation_cost = base_computation_cost
        self.initial_credits = initial_credits
        
        # State variables
        self.agents = self._initialize_agents()
        self.treasury_balance = initial_treasury
        self.round_num = 0
        
        # Treasury manager (PID controller)
        self.enable_adaptive_management = enable_adaptive_management
        if enable_adaptive_management:
            self.treasury_manager = TreasuryManagerAgent()
        
        # History tracking
        self.treasury_history = []
        self.promise_volume_history = []
        self.computation_cost_history = []
        self.op_cost_percentage_history = []
        self.revenue_history = []
        
        # Gas cost tracking (for improved scalability analysis)
        self.gas_costs = {
            'MAKE_PROMISE': 40000,
            'ASSESS_PROMISE': 25000,
            'UPDATE_MERIT': 15000,
            'TREASURY_UPDATE': 10000
        }
        self.gas_history = []

    def _initialize_agents(self) -> Dict[int, Agent]:
        agents = {}
        for i in range(self.n_agents):
            # Mix of agent types
            agent_type = np.random.choice(['honest', 'dishonest', 'variable'], 
                                        p=[0.7, 0.2, 0.1])
            
            if agent_type == 'honest':
                honesty_rate = np.random.uniform(0.9, 0.98)
            elif agent_type == 'dishonest':
                honesty_rate = np.random.uniform(0.3, 0.5)
            else:  # variable
                honesty_rate = np.random.uniform(0.5, 0.9)
            
            agent = Agent(
                id=i, 
                credits=self.initial_credits * np.random.uniform(0.8, 1.2),
                honesty_rate=honesty_rate
            )
            
            # Initialize merit
            for domain in self.domains:
                agent.merit[domain] = np.random.uniform(0.1, 0.3)
            
            agents[i] = agent
        return agents

    def calculate_stake_requirement(self, agent: Agent, domain: str, 
                                  promise_value: float) -> float:
        """Stake requirement that scales with promise value"""
        merit = agent.merit.get(domain, 0.1)
        discount = (merit ** 1.2) * 0.8  # Super-linear merit benefit
        
        # Base stake scales with promise value
        value_adjusted_stake = self.base_stake * (1 + np.log(1 + promise_value / 100))
        
        return value_adjusted_stake * (1 - discount)

    def generate_volatile_computation_cost(self) -> float:
        """Generate realistic volatile infrastructure costs"""
        # Log-normal distribution for cost spikes
        # Mean = base_cost, but with occasional large spikes
        
        # Base cost with daily variation
        daily_variation = np.random.uniform(0.8, 1.2)
        base = self.base_computation_cost * daily_variation
        
        # Add spikes (5% chance of major spike)
        if random.random() < 0.05:
            # Major spike (3-10x normal cost)
            spike_multiplier = lognorm.rvs(s=0.5, scale=5.0)
            return base * spike_multiplier
        elif random.random() < 0.15:
            # Minor spike (1.5-3x normal cost)
            spike_multiplier = np.random.uniform(1.5, 3.0)
            return base * spike_multiplier
        else:
            # Normal operation
            return base

    def simulate_round(self):
        self.round_num += 1
        promises_this_round = 0
        round_revenue = 0
        round_gas_used = 0

        # Generate infrastructure cost for this round
        computation_cost = self.generate_volatile_computation_cost()
        round_gas_used += self.gas_costs['TREASURY_UPDATE']

        # Adaptive management: adjust op_cost if enabled
        if self.enable_adaptive_management and self.round_num > 10:
            self.op_cost_percentage = self.treasury_manager.update_op_cost(
                self.treasury_balance,
                self.computation_cost_history,
                self.op_cost_percentage
            )

        # 1. Agents make promises
        for agent in self.agents.values():
            if agent.credits < self.base_stake * 0.5:  # Skip if too poor
                continue
            
            # Random domain and promise value
            domain = random.choice(self.domains)
            promise_value = np.random.gamma(2, 50) * (1 + hash(domain) % 3)
            
            stake = self.calculate_stake_requirement(agent, domain, promise_value)
            if agent.credits < stake:
                continue

            # Agent makes promise
            agent.credits -= stake
            promises_this_round += 1
            round_gas_used += self.gas_costs['MAKE_PROMISE']
            
            # Treasury collects operational cost
            op_cost = stake * self.op_cost_percentage
            self.treasury_balance += op_cost
            round_revenue += op_cost
            
            # Process outcome
            outcome_roll = np.random.random()
            if outcome_roll < agent.honesty_rate:  # Promise Kept
                # Return at-risk portion
                agent.credits += (stake - op_cost)
                
                # Update merit
                merit_before = agent.merit[domain]
                delta_merit = 0.02 * (1 - merit_before)
                agent.merit[domain] = min(1.0, merit_before + delta_merit)
                round_gas_used += self.gas_costs['UPDATE_MERIT']
                
            else:  # Promise Broken
                # Stake is lost, merit decreases
                merit_before = agent.merit[domain]
                delta_merit = -0.1 * merit_before
                agent.merit[domain] = max(0.0, merit_before + delta_merit)
                round_gas_used += self.gas_costs['UPDATE_MERIT']
            
            # Simulate assessment gas costs
            n_assessors = np.random.randint(3, 7)
            round_gas_used += n_assessors * self.gas_costs['ASSESS_PROMISE']

        # 2. Treasury pays infrastructure costs
        self.treasury_balance -= computation_cost
        
        # 3. Handle potential bankruptcy
        if self.treasury_balance < 0:
            print(f"⚠️  Treasury approaching insolvency at round {self.round_num}")
            # Emergency fee increase
            if self.enable_adaptive_management:
                self.op_cost_percentage = min(0.15, self.op_cost_percentage * 1.5)
        
        # 4. Record history
        self.treasury_history.append(self.treasury_balance)
        self.promise_volume_history.append(promises_this_round)
        self.computation_cost_history.append(computation_cost)
        self.op_cost_percentage_history.append(self.op_cost_percentage)
        self.revenue_history.append(round_revenue)
        self.gas_history.append(round_gas_used)

    def run(self):
        """Run the full simulation"""
        print(f"🏦 Starting Treasury Stress Test (Adaptive={self.enable_adaptive_management})")
        
        for i in range(self.n_rounds):
            self.simulate_round()
            
            if self.treasury_balance <= 0:
                print(f"💸 Treasury bankrupt at round {i+1}")
                break
                
            if i % 50 == 0:
                print(f"Round {i}: Treasury={self.treasury_balance:.0f}, "
                      f"OpCost={self.op_cost_percentage:.1%}, "
                      f"Promises={self.promise_volume_history[-1]}")
        
        return self.analyze_results()

    def analyze_results(self):
        """Comprehensive analysis of simulation results"""
        results = {
            'treasury_history': self.treasury_history,
            'promise_volume': self.promise_volume_history,
            'computation_costs': self.computation_cost_history,
            'op_cost_history': self.op_cost_percentage_history,
            'revenue_history': self.revenue_history,
            'gas_history': self.gas_history,
            'final_balance': self.treasury_history[-1] if self.treasury_history else 0,
            'survived_all_rounds': len(self.treasury_history) == self.n_rounds,
            'total_gas_used': sum(self.gas_history),
            'avg_gas_per_round': np.mean(self.gas_history) if self.gas_history else 0
        }
        
        # Calculate stability metrics
        if len(self.treasury_history) > 10:
            # Log-stability slope
            log_history = np.log([max(1, h) for h in self.treasury_history])
            slope, _, _, _, _ = stats.linregress(range(len(log_history)), log_history)
            results['stability_slope'] = slope
            
            # Volatility
            results['balance_volatility'] = np.std(self.treasury_history) / np.mean(self.treasury_history)
            
            # Cost spike resilience
            max_cost = max(self.computation_cost_history)
            avg_cost = np.mean(self.computation_cost_history)
            results['max_cost_spike'] = max_cost / avg_cost
        
        return results

    def plot_results(self):
        """Generate comprehensive visualization"""
        fig, axes = plt.subplots(2, 3, figsize=(18, 10))
        
        # 1. Treasury Balance Over Time
        ax = axes[0, 0]
        ax.plot(self.treasury_history, linewidth=2, color='darkblue')
        ax.axhline(y=0, color='red', linestyle='--', alpha=0.5)
        ax.fill_between(range(len(self.treasury_history)), 0, self.treasury_history, 
                       alpha=0.3, color='lightblue')
        ax.set_title('Treasury Balance Evolution', fontsize=14)
        ax.set_xlabel('Round')
        ax.set_ylabel('Credits')
        ax.grid(True, alpha=0.3)
        
        # 2. Infrastructure Costs (Volatile)
        ax = axes[0, 1]
        ax.plot(self.computation_cost_history, alpha=0.6, color='red', label='Actual')
        ax.axhline(y=self.base_computation_cost, color='black', linestyle='--', 
                  label='Baseline', alpha=0.5)
        
        # Show cost spikes
        spike_threshold = self.base_computation_cost * 2
        spike_rounds = [i for i, c in enumerate(self.computation_cost_history) if c > spike_threshold]
        spike_costs = [self.computation_cost_history[i] for i in spike_rounds]
        ax.scatter(spike_rounds, spike_costs, color='darkred', s=50, zorder=5, 
                  label='Cost Spikes')
        
        ax.set_title('Infrastructure Cost Volatility', fontsize=14)
        ax.set_xlabel('Round')
        ax.set_ylabel('Cost per Round')
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        # 3. Adaptive Op Cost
        ax = axes[0, 2]
        ax.plot(np.array(self.op_cost_percentage_history) * 100, linewidth=2, color='green')
        ax.set_title('Adaptive Operational Cost %', fontsize=14)
        ax.set_xlabel('Round')
        ax.set_ylabel('Op Cost %')
        ax.grid(True, alpha=0.3)
        
        # 4. Promise Volume
        ax = axes[1, 0]
        ax.plot(self.promise_volume_history, alpha=0.7, color='purple')
        ax.set_title('Promise Activity', fontsize=14)
        ax.set_xlabel('Round')
        ax.set_ylabel('Promises per Round')
        ax.grid(True, alpha=0.3)
        
        # 5. Revenue vs Costs
        ax = axes[1, 1]
        cumulative_revenue = np.cumsum(self.revenue_history)
        cumulative_costs = np.cumsum(self.computation_cost_history)
        
        ax.plot(cumulative_revenue, label='Cumulative Revenue', linewidth=2, color='green')
        ax.plot(cumulative_costs, label='Cumulative Costs', linewidth=2, color='red')
        ax.fill_between(range(len(cumulative_revenue)), 
                       cumulative_revenue, cumulative_costs, 
                       where=(cumulative_revenue >= cumulative_costs), 
                       color='lightgreen', alpha=0.3, label='Profit')
        ax.fill_between(range(len(cumulative_revenue)), 
                       cumulative_revenue, cumulative_costs, 
                       where=(cumulative_revenue < cumulative_costs), 
                       color='lightcoral', alpha=0.3, label='Loss')
        
        ax.set_title('Cumulative Revenue vs Costs', fontsize=14)
        ax.set_xlabel('Round')
        ax.set_ylabel('Credits')
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        # 6. Gas Usage (Scalability)
        ax = axes[1, 2]
        ax.plot(self.gas_history, alpha=0.6, color='orange')
        
        # Add trend line
        if len(self.gas_history) > 10:
            z = np.polyfit(range(len(self.gas_history)), self.gas_history, 1)
            p = np.poly1d(z)
            ax.plot(range(len(self.gas_history)), p(range(len(self.gas_history))), 
                   "--", color='darkorange', linewidth=2, label=f'Trend')
        
        ax.set_title('Gas Usage per Round', fontsize=14)
        ax.set_xlabel('Round')
        ax.set_ylabel('Gas Units')
        ax.legend()
        ax.grid(True, alpha=0.3)
        
        plt.tight_layout()
        plt.show()
        
        # Print summary statistics
        print("\n=== Treasury Stress Test Summary ===")
        print(f"Survival: {'✅ PASSED' if self.treasury_history[-1] > 0 else '❌ FAILED'}")
        print(f"Final Balance: {self.treasury_history[-1]:.0f} credits")
        print(f"Avg Infrastructure Cost: {np.mean(self.computation_cost_history):.0f}")
        print(f"Max Cost Spike: {max(self.computation_cost_history):.0f} "
              f"({max(self.computation_cost_history)/self.base_computation_cost:.1f}x baseline)")
        print(f"Final Op Cost: {self.op_cost_percentage_history[-1]:.1%}")
        print(f"Total Gas Used: {sum(self.gas_history):,} units")
        print(f"Avg Gas/Round: {np.mean(self.gas_history):,.0f} units")

# Comprehensive test suite
class TreasuryStressTestSuite:
    """Run multiple scenarios to test treasury robustness"""
    
    def __init__(self, seed: int = 42):
        self.seed = seed
        self.results = {}
    
    def run_all_tests(self):
        """Run comprehensive test scenarios"""
        
        # Test 1: Baseline with adaptive management
        print("\n📊 Test 1: Baseline with Adaptive Management")
        sim1 = ImprovedTreasuryStressTestSimulation(
            n_agents=100,
            n_rounds=300,
            seed=self.seed,
            enable_adaptive_management=True
        )
        self.results['adaptive'] = sim1.run()
        sim1.plot_results()
        
        # Test 2: Without adaptive management
        print("\n📊 Test 2: Fixed Op Cost (No Adaptation)")
        sim2 = ImprovedTreasuryStressTestSimulation(
            n_agents=100,
            n_rounds=300,
            seed=self.seed,
            enable_adaptive_management=False
        )
        self.results['fixed'] = sim2.run()
        
        # Test 3: High volatility stress test
        print("\n📊 Test 3: Extreme Volatility Scenario")
        sim3 = ImprovedTreasuryStressTestSimulation(
            n_agents=100,
            n_rounds=300,
            seed=self.seed + 1,
            base_computation_cost=300,  # Higher baseline
            enable_adaptive_management=True
        )
        self.results['high_volatility'] = sim3.run()
        
        # Test 4: Growth scenario
        print("\n📊 Test 4: Network Growth Scenario")
        sim4 = ImprovedTreasuryStressTestSimulation(
            n_agents=200,  # Double the agents
            n_rounds=300,
            seed=self.seed + 2,
            enable_adaptive_management=True
        )
        self.results['growth'] = sim4.run()
        
        self.print_comparison()
    
    def print_comparison(self):
        """Print comparative analysis"""
        print("\n" + "="*80)
        print("🔬 COMPARATIVE ANALYSIS")
        print("="*80)
        
        comparison_df = pd.DataFrame({
            scenario: {
                'Survived': results['survived_all_rounds'],
                'Final Balance': f"{results['final_balance']:,.0f}",
                'Stability': f"{results.get('stability_slope', 0):.4f}",
                'Max Spike': f"{results.get('max_cost_spike', 0):.1f}x",
                'Avg Gas/Round': f"{results.get('avg_gas_per_round', 0):,.0f}"
            }
            for scenario, results in self.results.items()
        }).T
        
        print(comparison_df)
        
        print("\n🎯 KEY FINDINGS:")
        
        # Compare adaptive vs fixed
        if self.results['adaptive']['final_balance'] > self.results['fixed']['final_balance']:
            improvement = (self.results['adaptive']['final_balance'] / 
                         self.results['fixed']['final_balance'] - 1) * 100
            print(f"✅ Adaptive management improved final balance by {improvement:.0f}%")
        
        # Check volatility resilience
        if self.results['high_volatility']['survived_all_rounds']:
            print("✅ Protocol survived extreme volatility with adaptive management")
        else:
            print("❌ Protocol failed under extreme volatility - needs stronger buffers")
        
        # Scalability assessment
        gas_per_agent_small = self.results['adaptive']['avg_gas_per_round'] / 100
        gas_per_agent_large = self.results['growth']['avg_gas_per_round'] / 200
        scaling_factor = gas_per_agent_large / gas_per_agent_small
        
        print(f"📈 Scaling efficiency: {scaling_factor:.2f}x gas per agent at 2x scale")
        if scaling_factor < 1.2:
            print("   ✅ Good sub-linear scaling achieved")
        else:
            print("   ⚠️  Scaling needs optimization")

if __name__ == "__main__":
    # Run the comprehensive test suite
    suite = TreasuryStressTestSuite(seed=42)
    suite.run_all_tests()