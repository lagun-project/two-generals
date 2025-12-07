/**
 * TGP Web Visualizer - Packet Visualizer Component
 *
 * D3.js-powered visualization for animating packets flowing
 * through the lossy channel between Alice and Bob.
 *
 * Features:
 * - Real-time packet animation
 * - Visual distinction between Alice->Bob and Bob->Alice
 * - Lost packet fade-out animation
 * - Delivery confirmation animation
 */

import * as d3 from 'd3';
import { Colors, Timing } from './types.js';

export class PacketVisualizer {
    /**
     * Create a new packet visualizer.
     * @param {string} svgSelector - CSS selector for the SVG element
     */
    constructor(svgSelector) {
        this.svg = d3.select(svgSelector);
        this.width = 400;
        this.height = 200;
        this.packets = new Map();

        this.colors = {
            alice: Colors.alice,
            bob: Colors.bob,
            channel: Colors.bgDark,
            text: Colors.text
        };

        this.setupSVG();
    }

    /**
     * Initialize the SVG with background, channel lines, and labels.
     */
    setupSVG() {
        // Clear existing content
        this.svg.selectAll('*').remove();

        // Define gradient for channel background
        const defs = this.svg.append('defs');

        const gradient = defs.append('linearGradient')
            .attr('id', 'channel-gradient')
            .attr('x1', '0%')
            .attr('x2', '100%');

        gradient.append('stop')
            .attr('offset', '0%')
            .attr('stop-color', this.colors.alice)
            .attr('stop-opacity', 0.2);

        gradient.append('stop')
            .attr('offset', '50%')
            .attr('stop-color', Colors.bgDark);

        gradient.append('stop')
            .attr('offset', '100%')
            .attr('stop-color', this.colors.bob)
            .attr('stop-opacity', 0.2);

        // Glow filter for delivered packets
        const glowFilter = defs.append('filter')
            .attr('id', 'packet-glow')
            .attr('x', '-50%')
            .attr('y', '-50%')
            .attr('width', '200%')
            .attr('height', '200%');

        glowFilter.append('feGaussianBlur')
            .attr('stdDeviation', '2')
            .attr('result', 'blur');

        const feMerge = glowFilter.append('feMerge');
        feMerge.append('feMergeNode').attr('in', 'blur');
        feMerge.append('feMergeNode').attr('in', 'SourceGraphic');

        // Background
        this.svg.append('rect')
            .attr('width', this.width)
            .attr('height', this.height)
            .attr('fill', 'url(#channel-gradient)');

        // Channel lines (dashed)
        this.svg.append('line')
            .attr('class', 'channel-line alice-to-bob')
            .attr('x1', 20)
            .attr('y1', 70)
            .attr('x2', 380)
            .attr('y2', 70)
            .attr('stroke', this.colors.alice)
            .attr('stroke-width', 2)
            .attr('stroke-dasharray', '5,5')
            .attr('opacity', 0.5);

        this.svg.append('line')
            .attr('class', 'channel-line bob-to-alice')
            .attr('x1', 20)
            .attr('y1', 130)
            .attr('x2', 380)
            .attr('y2', 130)
            .attr('stroke', this.colors.bob)
            .attr('stroke-width', 2)
            .attr('stroke-dasharray', '5,5')
            .attr('opacity', 0.5);

        // Direction labels
        this.svg.append('text')
            .attr('x', 200)
            .attr('y', 55)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.alice)
            .attr('font-size', '12px')
            .text('Alice -> Bob');

        this.svg.append('text')
            .attr('x', 200)
            .attr('y', 155)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.bob)
            .attr('font-size', '12px')
            .text('Bob -> Alice');

        // Packet container layer
        this.packetGroup = this.svg.append('g')
            .attr('class', 'packets');
    }

    /**
     * Add a new packet to the visualization.
     * @param {object} packet - Packet data with id, direction, msg, isLost
     */
    addPacket(packet) {
        const y = packet.direction === 'alice-to-bob' ? 70 : 130;
        const startX = packet.direction === 'alice-to-bob' ? 20 : 380;
        const endX = packet.direction === 'alice-to-bob' ? 380 : 20;
        const color = packet.direction === 'alice-to-bob' ? this.colors.alice : this.colors.bob;

        const group = this.packetGroup.append('g')
            .attr('class', 'packet')
            .attr('data-id', packet.id);

        // Packet shape (rounded rectangle)
        group.append('rect')
            .attr('x', -12)
            .attr('y', -10)
            .attr('width', 24)
            .attr('height', 20)
            .attr('rx', 4)
            .attr('fill', color)
            .attr('opacity', packet.isLost ? 0.4 : 1)
            .attr('filter', packet.isLost ? 'none' : 'url(#packet-glow)');

        // Packet type label
        group.append('text')
            .attr('text-anchor', 'middle')
            .attr('dy', 4)
            .attr('fill', '#fff')
            .attr('font-size', '10px')
            .attr('font-weight', 'bold')
            .text(packet.msg.type);

        // Initial position
        const x = startX + (endX - startX) * packet.progress;
        group.attr('transform', `translate(${x}, ${y})`);

        // Store packet data for updates
        this.packets.set(packet.id, {
            group,
            startX,
            endX,
            y,
            packet,
            color
        });
    }

    /**
     * Update packet position during animation.
     * @param {object} packet - Packet data with updated progress
     */
    updatePacket(packet) {
        const data = this.packets.get(packet.id);
        if (!data) return;

        const x = data.startX + (data.endX - data.startX) * packet.progress;
        data.group.attr('transform', `translate(${x}, ${data.y})`);

        // Fade out lost packets as they travel
        if (packet.isLost && packet.progress > 0.3) {
            const fadeProgress = (packet.progress - 0.3) / 0.4;
            data.group.select('rect')
                .attr('opacity', Math.max(0, 0.4 - fadeProgress * 0.4));
        }
    }

    /**
     * Remove a packet from the visualization (on arrival or loss).
     * @param {object} packet - Packet data
     */
    removePacket(packet) {
        const data = this.packets.get(packet.id);
        if (!data) return;

        if (packet.isLost) {
            // Lost packet: fade out and remove
            data.group.transition()
                .duration(Timing.normal)
                .attr('opacity', 0)
                .remove();
        } else {
            // Delivered packet: pop animation
            data.group.transition()
                .duration(Timing.fast)
                .attr('transform', `translate(${data.endX}, ${data.y}) scale(1.3)`)
                .transition()
                .duration(Timing.fast)
                .attr('opacity', 0)
                .remove();

            // Add delivery ripple effect
            this.addDeliveryEffect(data.endX, data.y, data.color);
        }

        this.packets.delete(packet.id);
    }

    /**
     * Add a visual ripple effect when a packet is delivered.
     */
    addDeliveryEffect(x, y, color) {
        const ripple = this.svg.append('circle')
            .attr('cx', x)
            .attr('cy', y)
            .attr('r', 8)
            .attr('fill', 'none')
            .attr('stroke', color)
            .attr('stroke-width', 2)
            .attr('opacity', 0.8);

        ripple.transition()
            .duration(Timing.proof)
            .attr('r', 25)
            .attr('opacity', 0)
            .remove();
    }

    /**
     * Clear all packets from the visualization.
     */
    clear() {
        this.packetGroup.selectAll('.packet').remove();
        this.packets.clear();
    }

    /**
     * Resize the visualization.
     * @param {number} width - New width
     * @param {number} height - New height
     */
    resize(width, height) {
        this.width = width;
        this.height = height;
        this.svg.attr('viewBox', `0 0 ${width} ${height}`);
        // Re-setup would be needed for full resize support
    }

    /**
     * Get current packet count.
     * @returns {number} Number of packets in flight
     */
    getPacketCount() {
        return this.packets.size;
    }
}

/**
 * Create a standalone packet visualizer with controls.
 * @param {string} containerId - Container element ID
 * @returns {object} Visualizer instance and control methods
 */
export function createPacketVisualizerWithControls(containerId) {
    const container = document.getElementById(containerId);
    if (!container) {
        console.error(`Container not found: ${containerId}`);
        return null;
    }

    // Create SVG element
    container.innerHTML = `
        <div class="packet-viz-wrapper">
            <svg id="${containerId}-svg" viewBox="0 0 400 200"></svg>
            <div class="packet-viz-stats">
                <span>Packets in flight: <strong id="${containerId}-count">0</strong></span>
            </div>
        </div>
    `;

    const visualizer = new PacketVisualizer(`#${containerId}-svg`);
    const countEl = document.getElementById(`${containerId}-count`);

    return {
        visualizer,
        updateCount() {
            countEl.textContent = visualizer.getPacketCount();
        },
        addPacket(packet) {
            visualizer.addPacket(packet);
            this.updateCount();
        },
        updatePacket(packet) {
            visualizer.updatePacket(packet);
        },
        removePacket(packet) {
            visualizer.removePacket(packet);
            this.updateCount();
        },
        clear() {
            visualizer.clear();
            this.updateCount();
        }
    };
}
