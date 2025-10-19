from abm import AgencyProtocolSimulation
import json

def run_all_simulations():
    all_summaries = []

    # Scenario 1: Normal operation
    print("Running Scenario 1: Normal operation")
    sim1 = AgencyProtocolSimulation(n_agents=100, n_domains=5)
    summary1 = sim1.get_simulation_summary(n_rounds=100)
    all_summaries.append({"scenario": "Normal Operation", **summary1})

    # Scenario 2: Small coalition attack at round 50
    print("Running Scenario 2: Small coalition attack")
    sim2 = AgencyProtocolSimulation(n_agents=100, n_domains=5)
    summary2 = sim2.get_simulation_summary(n_rounds=100, coalition_round=50, coalition_size=10)
    all_summaries.append({"scenario": "Small Coalition Attack", **summary2})

    # Scenario 3: Large coalition attack at round 50
    print("Running Scenario 3: Large coalition attack")
    sim3 = AgencyProtocolSimulation(n_agents=100, n_domains=5)
    summary3 = sim3.get_simulation_summary(n_rounds=100, coalition_round=50, coalition_size=30)
    all_summaries.append({"scenario": "Large Coalition Attack", **summary3})

    # Scenario 4: Early coalition attack (round 20)
    print("Running Scenario 4: Early coalition attack")
    sim4 = AgencyProtocolSimulation(n_agents=100, n_domains=5)
    summary4 = sim4.get_simulation_summary(n_rounds=100, coalition_round=20, coalition_size=20)
    all_summaries.append({"scenario": "Early Coalition Attack", **summary4})

    # Scenario 5: Late coalition attack (round 80)
    print("Running Scenario 5: Late coalition attack")
    sim5 = AgencyProtocolSimulation(n_agents=100, n_domains=5)
    summary5 = sim5.get_simulation_summary(n_rounds=100, coalition_round=80, coalition_size=20)
    all_summaries.append({"scenario": "Late Coalition Attack", **summary5})

    print("\n--- All Simulation Summaries ---")
    print(json.dumps(all_summaries, indent=2))

if __name__ == "__main__":
    run_all_simulations()
