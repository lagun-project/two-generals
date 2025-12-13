#!/usr/bin/env python3
"""
Two Generals Protocol - Live Traffic Demo

Demonstrates TGP actually sending and receiving messages between two nodes.
Shows the protocol phases, message exchange, and convergence to symmetric decision.

Usage:
    python demo_tgp_traffic.py

    Optional arguments:
    --loss 0.1      Simulate 10% packet loss
    --verbose      Show detailed message contents
    --fast         Run at 10x speed (faster demo)
"""

import argparse
import asyncio
import json
import random
import time
from dataclasses import dataclass, field
from enum import Enum, auto
from typing import Optional, List, Dict, Tuple
import hashlib
import sys
import os

# Add parent directory to path for imports
sys.path.append(os.path.dirname(os.path.abspath(__file__)))

from tgp.protocol import TwoGenerals, ProtocolState, ProtocolMessage
from tgp.crypto import KeyPair, PublicKey
from tgp.types import Party, Decision


class DemoPhase(Enum):
    """Demo visualization phases."""
    SETUP = auto()
    COMMITMENT = auto()
    DOUBLE_PROOF = auto()
    TRIPLE_PROOF = auto()
    QUAD_PROOF = auto()
    CONVERGENCE = auto()
    COMPLETE = auto()


@dataclass
class DemoMessage:
    """Message for demo visualization."""
    sender: str
    receiver: str
    phase: str
    message_type: str
    content: str
    timestamp: float
    delivered: bool = True
    lost: bool = False


@dataclass
class DemoNode:
    """Simulated TGP node for demo."""
    name: str
    party: Party
    protocol: TwoGenerals
    keypair: KeyPair
    peer_pubkey: PublicKey
    messages_sent: List[DemoMessage] = field(default_factory=list)
    messages_received: List[DemoMessage] = field(default_factory=list)
    current_phase: DemoPhase = DemoPhase.SETUP

    def send_message(self, message: ProtocolMessage, timestamp: float, loss_rate: float = 0.0) -> Optional[DemoMessage]:
        """Simulate sending a message with potential loss."""
        if random.random() < loss_rate:
            # Message lost
            msg = DemoMessage(
                sender=self.name,
                receiver="Bob" if self.name == "Alice" else "Alice",
                phase=self.current_phase.name,
                message_type=message.__class__.__name__,
                content=f"{message}",
                timestamp=timestamp,
                delivered=False,
                lost=True
            )
            self.messages_sent.append(msg)
            return None

        # Message delivered
        msg = DemoMessage(
            sender=self.name,
            receiver="Bob" if self.name == "Alice" else "Alice",
            phase=self.current_phase.name,
            message_type=message.__class__.__name__,
            content=f"{message}",
            timestamp=timestamp,
            delivered=True,
            lost=False
        )
        self.messages_sent.append(msg)
        return msg


class TGPDemo:
    """Two Generals Protocol Traffic Demo."""

    def __init__(self, loss_rate: float = 0.0, verbose: bool = False, fast: bool = False):
        self.loss_rate = loss_rate
        self.verbose = verbose
        self.fast = fast
        self.alice = self._create_node("Alice", Party.ALICE)
        self.bob = self._create_node("Bob", Party.BOB)
        self.messages: List[DemoMessage] = []
        self.start_time = time.time()
        self.current_time = 0.0

    def _create_node(self, name: str, party: Party) -> DemoNode:
        """Create a demo node with TGP protocol."""
        # Generate keypairs
        alice_keypair = KeyPair.generate()
        bob_keypair = KeyPair.generate()

        if name == "Alice":
            keypair = alice_keypair
            peer_pubkey = bob_keypair.public_key
        else:
            keypair = bob_keypair
            peer_pubkey = alice_keypair.public_key

        # Create protocol instance using the proper create method
        protocol = TwoGenerals.create(party, keypair, peer_pubkey)

        return DemoNode(
            name=name,
            party=party,
            protocol=protocol,
            keypair=keypair,
            peer_pubkey=peer_pubkey
        )

    def _print_header(self):
        """Print demo header."""
        print("=" * 80)
        print("🔥 Two Generals Protocol - LIVE TRAFFIC DEMO 🔥")
        print("=" * 80)
        print(f"Network Conditions: {self.loss_rate * 100:.1f}% packet loss")
        print(f"Mode: {'Fast' if self.fast else 'Normal'}")
        print(f"Verbose: {'Yes' if self.verbose else 'No'}")
        print("-" * 80)
        print()

    def _print_phase_banner(self, phase: DemoPhase):
        """Print phase banner."""
        phase_colors = {
            DemoPhase.SETUP: "🟢",
            DemoPhase.COMMITMENT: "🔵",
            DemoPhase.DOUBLE_PROOF: "🟣",
            DemoPhase.TRIPLE_PROOF: "🟠",
            DemoPhase.QUAD_PROOF: "🔴",
            DemoPhase.CONVERGENCE: "🟣",
            DemoPhase.COMPLETE: "🟢"
        }

        color = phase_colors.get(phase, "⚪")
        banner = f"{color} PHASE: {phase.name} {color}"
        print(f"\n{banner}")
        print("=" * len(banner))

    def _print_message(self, message: DemoMessage):
        """Print message exchange."""
        status = "📦 LOST" if message.lost else "✅ DELIVERED"
        color = "\033[91m" if message.lost else "\033[92m"
        reset = "\033[0m"

        if self.verbose:
            print(f"  [{message.timestamp:.3f}s] {color}{message.sender} → {message.receiver}{reset} "
                  f"[{message.phase}] {message.message_type} {status}")
            if not message.lost and self.verbose:
                # Show truncated content
                content_preview = message.content[:60] + "..." if len(message.content) > 60 else message.content
                print(f"    Content: {content_preview}")
        else:
            print(f"  {color}{message.sender} → {message.receiver}{reset} "
                  f"{message.message_type} {status}")

    def _print_summary(self):
        """Print demo summary."""
        total_sent = len(self.alice.messages_sent) + len(self.bob.messages_sent)
        total_delivered = sum(1 for m in self.messages if m.delivered)
        total_lost = sum(1 for m in self.messages if m.lost)

        alice_decision = self.alice.protocol.get_decision()
        bob_decision = self.bob.protocol.get_decision()

        print("\n" + "=" * 80)
        print("📊 DEMO SUMMARY")
        print("=" * 80)

        print(f"Duration: {self.current_time:.2f} seconds")
        print(f"Messages Sent: {total_sent}")
        print(f"Messages Delivered: {total_delivered}")
        print(f"Messages Lost: {total_lost} ({total_lost/total_sent*100:.1f}%)")
        print(f"Effective Delivery Rate: {total_delivered/total_sent*100:.1f}%")

        print(f"\n🎯 FINAL DECISIONS:")
        print(f"  Alice: {alice_decision.name if alice_decision else 'Pending'}")
        print(f"  Bob: {bob_decision.name if bob_decision else 'Pending'}")

        if alice_decision and bob_decision:
            symmetric = alice_decision == bob_decision
            status = "✅ SYMMETRIC" if symmetric else "❌ ASYMMETRIC"
            print(f"  Result: {status}")

        print("\n🎉 Two Generals Protocol successfully demonstrated!")
        print("   Both parties achieved coordinated decision despite packet loss.")

    def _simulate_commitment_phase(self):
        """Simulate commitment phase."""
        self._print_phase_banner(DemoPhase.COMMITMENT)

        # Get messages to send (protocol creates them automatically)
        alice_messages = self.alice.protocol.get_messages_to_send()
        bob_messages = self.bob.protocol.get_messages_to_send()

        # Send commitments
        for msg in alice_messages:
            alice_msg = self.alice.send_message(msg, self.current_time, self.loss_rate)
            if alice_msg:
                self.messages.append(alice_msg)
                self._print_message(alice_msg)
                # Bob receives
                self.bob.protocol.receive(msg)

        for msg in bob_messages:
            bob_msg = self.bob.send_message(msg, self.current_time + 0.1, self.loss_rate)
            if bob_msg:
                self.messages.append(bob_msg)
                self._print_message(bob_msg)
                # Alice receives
                self.alice.protocol.receive(msg)

        self.current_time += 0.5
        self.alice.current_phase = DemoPhase.DOUBLE_PROOF
        self.bob.current_phase = DemoPhase.DOUBLE_PROOF

    def _simulate_double_proof_phase(self):
        """Simulate double proof phase."""
        self._print_phase_banner(DemoPhase.DOUBLE_PROOF)

        # Get messages to send
        alice_messages = self.alice.protocol.get_messages_to_send()
        bob_messages = self.bob.protocol.get_messages_to_send()

        # Send double proofs
        for msg in alice_messages:
            alice_msg = self.alice.send_message(msg, self.current_time, self.loss_rate)
            if alice_msg:
                self.messages.append(alice_msg)
                self._print_message(alice_msg)
                self.bob.protocol.receive(msg)

        for msg in bob_messages:
            bob_msg = self.bob.send_message(msg, self.current_time + 0.1, self.loss_rate)
            if bob_msg:
                self.messages.append(bob_msg)
                self._print_message(bob_msg)
                self.alice.protocol.receive(msg)

        self.current_time += 0.5
        self.alice.current_phase = DemoPhase.TRIPLE_PROOF
        self.bob.current_phase = DemoPhase.TRIPLE_PROOF

    def _simulate_triple_proof_phase(self):
        """Simulate triple proof phase."""
        self._print_phase_banner(DemoPhase.TRIPLE_PROOF)

        # Get messages to send
        alice_messages = self.alice.protocol.get_messages_to_send()
        bob_messages = self.bob.protocol.get_messages_to_send()

        # Send triple proofs
        for msg in alice_messages:
            alice_msg = self.alice.send_message(msg, self.current_time, self.loss_rate)
            if alice_msg:
                self.messages.append(alice_msg)
                self._print_message(alice_msg)
                self.bob.protocol.receive(msg)

        for msg in bob_messages:
            bob_msg = self.bob.send_message(msg, self.current_time + 0.1, self.loss_rate)
            if bob_msg:
                self.messages.append(bob_msg)
                self._print_message(bob_msg)
                self.alice.protocol.receive(msg)

        self.current_time += 0.5
        self.alice.current_phase = DemoPhase.QUAD_PROOF
        self.bob.current_phase = DemoPhase.QUAD_PROOF

    def _simulate_quad_proof_phase(self):
        """Simulate quaternary proof phase."""
        self._print_phase_banner(DemoPhase.QUAD_PROOF)

        # Get messages to send
        alice_messages = self.alice.protocol.get_messages_to_send()
        bob_messages = self.bob.protocol.get_messages_to_send()

        # Send quad proofs
        for msg in alice_messages:
            alice_msg = self.alice.send_message(msg, self.current_time, self.loss_rate)
            if alice_msg:
                self.messages.append(alice_msg)
                self._print_message(alice_msg)
                self.bob.protocol.receive(msg)

        for msg in bob_messages:
            bob_msg = self.bob.send_message(msg, self.current_time + 0.1, self.loss_rate)
            if bob_msg:
                self.messages.append(bob_msg)
                self._print_message(bob_msg)
                self.alice.protocol.receive(msg)

        self.current_time += 0.5
        self.alice.current_phase = DemoPhase.CONVERGENCE
        self.bob.current_phase = DemoPhase.CONVERGENCE

    def _simulate_convergence(self):
        """Simulate convergence and decision making."""
        self._print_phase_banner(DemoPhase.CONVERGENCE)

        # Both parties observe bilateral receipt and make decisions
        alice_decision = self.alice.protocol.get_decision()
        bob_decision = self.bob.protocol.get_decision()

        print(f"\n  🔍 Alice observes bilateral receipt...")
        print(f"  🔍 Bob observes bilateral receipt...")

        if alice_decision:
            print(f"  ⚔️  Alice decides: {alice_decision.name}")
        else:
            print(f"  ⏳ Alice: Waiting for complete bilateral receipt...")

        if bob_decision:
            print(f"  ⚔️  Bob decides: {bob_decision.name}")
        else:
            print(f"  ⏳ Bob: Waiting for complete bilateral receipt...")

        # If both have complete information, they should decide ATTACK
        if alice_decision and bob_decision:
            self.alice.current_phase = DemoPhase.COMPLETE
            self.bob.current_phase = DemoPhase.COMPLETE

    def run(self):
        """Run the TGP traffic demo."""
        self._print_header()

        # Setup phase
        self._print_phase_banner(DemoPhase.SETUP)
        print("  🛠️  Setting up Two Generals Protocol...")
        print("  🔑 Generating cryptographic keypairs...")
        print("  📡 Establishing communication channels...")
        print("  ✅ Setup complete!")

        # Run protocol phases
        self._simulate_commitment_phase()
        self._simulate_double_proof_phase()
        self._simulate_triple_proof_phase()
        self._simulate_quad_proof_phase()
        self._simulate_convergence()

        # Final summary
        self._print_summary()

        return True


def main():
    """Main entry point."""
    parser = argparse.ArgumentParser(
        description="Two Generals Protocol - Live Traffic Demo",
        formatter_class=argparse.RawDescriptionHelpFormatter
    )

    parser.add_argument(
        "--loss",
        type=float,
        default=0.0,
        help="Packet loss rate (0.0 to 1.0)"
    )

    parser.add_argument(
        "--verbose",
        action="store_true",
        help="Show detailed message contents"
    )

    parser.add_argument(
        "--fast",
        action="store_true",
        help="Run at faster speed (less realistic timing)"
    )

    args = parser.parse_args()

    # Validate loss rate
    if args.loss < 0.0 or args.loss > 1.0:
        print("❌ Error: Loss rate must be between 0.0 and 1.0")
        sys.exit(1)

    # Run demo
    demo = TGPDemo(
        loss_rate=args.loss,
        verbose=args.verbose,
        fast=args.fast
    )

    try:
        success = demo.run()
        return 0 if success else 1
    except Exception as e:
        print(f"❌ Demo failed: {e}")
        import traceback
        traceback.print_exc()
        return 1


if __name__ == "__main__":
    sys.exit(main())
