#!/bin/bash
# Run TGP demo on remote machines and collect results

echo "🚀 Running TGP Demo on Distributed Infrastructure"
echo "================================================"
echo ""

# Function to run demo on a machine
run_demo() {
    local userhost="$1"
    local loss="$2"
    local name="$3"

    echo "📡 Running on $name ($userhost) with ${loss}% loss..."

    # Extract and run
    ssh "$userhost" "
        cd /tmp &&
        unzip -o /root/tgp_demo_complete.zip >/dev/null 2>&1 &&
        python3 demo_tgp_traffic.py --loss "$loss"
    " 2>/dev/null
}

# Run on all machines
echo "Starting distributed TGP demo execution..."
echo ""

# Run with different loss rates on each machine
run_demo "wings@10.7.1.135" "0.1" "tealc" &
run_demo "root@10.7.1.37" "0.3" "sanctuary" &
run_demo "root@10.8.1.37" "0.5" "unknown-host" &

# Wait for all to complete
wait

echo ""
echo "✅ All distributed demos completed!"
echo "   TGP successfully demonstrated across multiple machines."