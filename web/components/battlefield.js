/**
 * TGP Web Visualizer - Battlefield Animation Component
 *
 * Visual representation of the Two Generals Problem scenario:
 * - Two armies positioned on opposite sides of a valley
 * - An enemy city in the center
 * - Messengers attempting to cross enemy territory
 * - The coordination dilemma: attack together or die separately
 *
 * This is the "hook" animation that explains why the problem matters.
 */

import * as d3 from 'd3';
import { Colors, createEventEmitter } from './types.js';
import { createAnimationControls } from './animation-controls.js';

export class BattlefieldScene {
    /**
     * Create a battlefield scene visualization.
     * @param {string|HTMLElement} container - Container element or selector
     */
    constructor(container) {
        this.container = typeof container === 'string'
            ? d3.select(container)
            : d3.select(container);

        this.width = 800;
        this.height = 450;
        this.svg = null;
        this.isAnimating = false;
        this.animationFrame = null;
        this.messengers = [];
        this.messengerIdCounter = 0;

        this.colors = {
            sky: '#1a1a2e',
            mountain: '#16213e',
            ground: '#1f4037',
            alice: Colors.alice,
            bob: Colors.bob,
            enemy: '#f85149',
            messenger: Colors.commitment,
            text: Colors.text,
            muted: Colors.muted
        };

        this.state = {
            messagesAttempted: 0,
            messagesLost: 0,
            messagesDelivered: 0
        };

        // Animation speed control
        this.speed = 1.0;
        this.isPaused = false;
        this.controls = null;

        // Event emitter
        const emitter = createEventEmitter();
        this.on = emitter.on;
        this.off = emitter.off;
        this.emit = emitter.emit;
    }

    /**
     * Initialize and render the battlefield scene.
     */
    init() {
        this.container.html('');

        // Create animation controls
        const containerEl = this.container.node();
        this.controls = createAnimationControls({
            container: containerEl,
            defaultSpeed: 1.0,
            minSpeed: 0.25,
            maxSpeed: 2.0,
            step: 0.25,
            onSpeedChange: (speed) => {
                this.speed = speed;
            },
            onPlayPause: (isPlaying) => {
                this.isPaused = !isPlaying;
            },
            onReset: () => {
                this.reset();
            }
        });

        this.svg = this.container.append('svg')
            .attr('viewBox', `0 0 ${this.width} ${this.height}`)
            .attr('preserveAspectRatio', 'xMidYMid meet')
            .attr('class', 'battlefield-svg')
            .style('width', '100%')
            .style('max-width', `${this.width}px`)
            .style('height', 'auto');

        this.drawBackground();
        this.drawMountains();
        this.drawEnemyCity();
        this.drawArmies();
        this.drawUI();
        this.drawNarrative();

        return this;
    }

    /**
     * Draw the sky background with stars.
     */
    drawBackground() {
        const defs = this.svg.append('defs');

        // Sky gradient
        const skyGradient = defs.append('linearGradient')
            .attr('id', 'bf-sky-gradient')
            .attr('x1', '0%').attr('y1', '0%')
            .attr('x2', '0%').attr('y2', '100%');

        skyGradient.append('stop')
            .attr('offset', '0%')
            .attr('stop-color', '#0f0f23');

        skyGradient.append('stop')
            .attr('offset', '100%')
            .attr('stop-color', '#1a1a2e');

        // Background
        this.svg.append('rect')
            .attr('width', this.width)
            .attr('height', this.height)
            .attr('fill', 'url(#bf-sky-gradient)');

        // Stars
        const starGroup = this.svg.append('g').attr('class', 'stars');
        for (let i = 0; i < 50; i++) {
            starGroup.append('circle')
                .attr('cx', Math.random() * this.width)
                .attr('cy', Math.random() * this.height * 0.4)
                .attr('r', Math.random() * 1.5 + 0.5)
                .attr('fill', '#fff')
                .attr('opacity', Math.random() * 0.5 + 0.3);
        }
    }

    /**
     * Draw mountain silhouettes.
     */
    drawMountains() {
        // Background mountains
        this.svg.append('path')
            .attr('d', `
                M0,200
                Q100,150 200,180
                Q300,120 400,160
                Q500,100 600,150
                Q700,130 800,170
                L800,${this.height} L0,${this.height} Z
            `)
            .attr('fill', this.colors.mountain)
            .attr('opacity', 0.8);

        // Foreground terrain
        this.svg.append('path')
            .attr('d', `
                M0,280
                Q100,250 200,270
                Q400,220 600,260
                Q700,240 800,260
                L800,${this.height} L0,${this.height} Z
            `)
            .attr('fill', this.colors.ground);
    }

    /**
     * Draw the enemy city in the center.
     */
    drawEnemyCity() {
        const centerX = this.width / 2;
        const cityY = 270;

        const cityGroup = this.svg.append('g').attr('class', 'enemy-city');

        // City walls
        cityGroup.append('rect')
            .attr('x', centerX - 60)
            .attr('y', cityY)
            .attr('width', 120)
            .attr('height', 60)
            .attr('fill', '#2d1f1f')
            .attr('stroke', this.colors.enemy)
            .attr('stroke-width', 2)
            .attr('rx', 4);

        // Towers
        [centerX - 50, centerX + 50].forEach(x => {
            cityGroup.append('rect')
                .attr('x', x - 10)
                .attr('y', cityY - 20)
                .attr('width', 20)
                .attr('height', 80)
                .attr('fill', '#2d1f1f')
                .attr('stroke', this.colors.enemy)
                .attr('stroke-width', 2);

            // Tower top
            cityGroup.append('polygon')
                .attr('points', `${x - 12},${cityY - 20} ${x},${cityY - 35} ${x + 12},${cityY - 20}`)
                .attr('fill', this.colors.enemy);
        });

        // Enemy flag
        cityGroup.append('line')
            .attr('x1', centerX)
            .attr('y1', cityY - 10)
            .attr('x2', centerX)
            .attr('y2', cityY - 50)
            .attr('stroke', '#8b949e')
            .attr('stroke-width', 2);

        cityGroup.append('polygon')
            .attr('points', `${centerX},${cityY - 50} ${centerX + 25},${cityY - 40} ${centerX},${cityY - 30}`)
            .attr('fill', this.colors.enemy);

        // City label
        cityGroup.append('text')
            .attr('x', centerX)
            .attr('y', cityY + 85)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.enemy)
            .attr('font-size', '12px')
            .attr('font-weight', 'bold')
            .text('ENEMY STRONGHOLD');

        // Danger zone indicator
        cityGroup.append('ellipse')
            .attr('cx', centerX)
            .attr('cy', cityY + 20)
            .attr('rx', 150)
            .attr('ry', 80)
            .attr('fill', 'none')
            .attr('stroke', this.colors.enemy)
            .attr('stroke-width', 1)
            .attr('stroke-dasharray', '4,4')
            .attr('opacity', 0.5);
    }

    /**
     * Draw the two armies.
     */
    drawArmies() {
        // Alice's army (left side)
        this.aliceGroup = this.svg.append('g').attr('class', 'alice-army');
        this.drawArmy(this.aliceGroup, 100, 300, this.colors.alice, "ALICE'S ARMY", 'left');

        // Bob's army (right side)
        this.bobGroup = this.svg.append('g').attr('class', 'bob-army');
        this.drawArmy(this.bobGroup, 700, 300, this.colors.bob, "BOB'S ARMY", 'right');

        // Messenger layer
        this.messengerLayer = this.svg.append('g').attr('class', 'messengers');
    }

    /**
     * Draw a single army.
     */
    drawArmy(group, x, y, color, label, side) {
        // Army tent/camp
        group.append('polygon')
            .attr('points', `${x - 30},${y + 20} ${x},${y - 20} ${x + 30},${y + 20}`)
            .attr('fill', color)
            .attr('opacity', 0.8);

        // Soldiers
        const soldiers = [-20, 0, 20, -10, 10];
        soldiers.forEach((offset, i) => {
            const sx = x + offset + (side === 'left' ? 50 : -50);
            const sy = y + 15 + (i % 2) * 10;

            // Head
            group.append('circle')
                .attr('cx', sx)
                .attr('cy', sy - 8)
                .attr('r', 6)
                .attr('fill', color);

            // Body
            group.append('rect')
                .attr('x', sx - 4)
                .attr('y', sy - 2)
                .attr('width', 8)
                .attr('height', 12)
                .attr('fill', color)
                .attr('rx', 2);
        });

        // Flag
        group.append('line')
            .attr('x1', x)
            .attr('y1', y - 20)
            .attr('x2', x)
            .attr('y2', y - 60)
            .attr('stroke', '#8b949e')
            .attr('stroke-width', 2);

        group.append('rect')
            .attr('x', side === 'left' ? x : x - 25)
            .attr('y', y - 60)
            .attr('width', 25)
            .attr('height', 15)
            .attr('fill', color);

        // Label
        group.append('text')
            .attr('x', x)
            .attr('y', y + 50)
            .attr('text-anchor', 'middle')
            .attr('fill', color)
            .attr('font-size', '11px')
            .attr('font-weight', 'bold')
            .text(label);

        // Status
        group.append('text')
            .attr('class', 'status')
            .attr('x', x)
            .attr('y', y + 65)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.muted)
            .attr('font-size', '10px')
            .text('Awaiting coordination...');
    }

    /**
     * Draw the control panel UI.
     */
    drawUI() {
        const panel = this.svg.append('g')
            .attr('class', 'control-panel')
            .attr('transform', 'translate(20, 20)');

        panel.append('rect')
            .attr('width', 200)
            .attr('height', 80)
            .attr('fill', '#161b22')
            .attr('stroke', '#30363d')
            .attr('stroke-width', 1)
            .attr('rx', 8)
            .attr('opacity', 0.9);

        panel.append('text')
            .attr('x', 10)
            .attr('y', 25)
            .attr('fill', this.colors.text)
            .attr('font-size', '12px')
            .attr('font-weight', 'bold')
            .text('THE DILEMMA');

        panel.append('text')
            .attr('x', 10)
            .attr('y', 45)
            .attr('fill', this.colors.muted)
            .attr('font-size', '10px')
            .text('Messages attempted: ');

        panel.append('text')
            .attr('class', 'messages-count')
            .attr('x', 120)
            .attr('y', 45)
            .attr('fill', this.colors.messenger)
            .attr('font-size', '10px')
            .attr('font-weight', 'bold')
            .text('0');

        panel.append('text')
            .attr('x', 10)
            .attr('y', 60)
            .attr('fill', this.colors.muted)
            .attr('font-size', '10px')
            .text('Messages lost: ');

        panel.append('text')
            .attr('class', 'lost-count')
            .attr('x', 90)
            .attr('y', 60)
            .attr('fill', this.colors.enemy)
            .attr('font-size', '10px')
            .attr('font-weight', 'bold')
            .text('0');
    }

    /**
     * Draw narrative text at bottom.
     */
    drawNarrative() {
        this.narrative = this.svg.append('g')
            .attr('class', 'narrative')
            .attr('transform', `translate(${this.width / 2}, ${this.height - 40})`);

        this.narrative.append('text')
            .attr('class', 'narrative-text')
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.text)
            .attr('font-size', '14px')
            .text('Two armies must coordinate an attack. If only one attacks, they will be destroyed.');

        this.narrative.append('text')
            .attr('class', 'narrative-subtext')
            .attr('y', 20)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.muted)
            .attr('font-size', '11px')
            .text('But every messenger sent through enemy territory might be captured...');
    }

    /**
     * Send a messenger across the battlefield.
     * @param {boolean} fromAlice - True if from Alice to Bob
     * @param {number} lossRate - Probability of loss (0-1)
     */
    sendMessenger(fromAlice = true, lossRate = 0.5) {
        this.state.messagesAttempted++;
        this.svg.select('.messages-count').text(this.state.messagesAttempted);

        const startX = fromAlice ? 150 : 650;
        const endX = fromAlice ? 650 : 150;
        const startY = 310;
        const isLost = Math.random() < lossRate;

        const id = this.messengerIdCounter++;

        // Create messenger group
        const messenger = this.messengerLayer.append('g')
            .attr('class', `messenger messenger-${id}`)
            .attr('transform', `translate(${startX}, ${startY})`);

        // Messenger icon
        messenger.append('circle')
            .attr('r', 8)
            .attr('fill', this.colors.messenger);

        messenger.append('text')
            .attr('text-anchor', 'middle')
            .attr('dy', 4)
            .attr('fill', '#fff')
            .attr('font-size', '10px')
            .text(fromAlice ? '>' : '<');

        messenger.append('text')
            .attr('y', -15)
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.messenger)
            .attr('font-size', '9px')
            .text(fromAlice ? 'MSG' : 'ACK');

        // Track messenger
        this.messengers.push({ id, messenger, startX, endX, progress: 0, isLost, startY });

        const lossPoint = 0.3 + Math.random() * 0.4;

        const animate = () => {
            const m = this.messengers.find(msg => msg.id === id);
            if (!m) return;

            // Respect pause state
            if (this.isPaused) {
                requestAnimationFrame(animate);
                return;
            }

            // Apply speed multiplier
            m.progress += 0.01 * this.speed;
            const x = m.startX + (m.endX - m.startX) * m.progress;
            const y = m.startY + Math.sin(m.progress * Math.PI) * -30;

            m.messenger.attr('transform', `translate(${x}, ${y})`);

            if (m.isLost && m.progress >= lossPoint) {
                this.state.messagesLost++;
                this.svg.select('.lost-count').text(this.state.messagesLost);

                m.messenger.transition()
                    .duration(300)
                    .attr('opacity', 0)
                    .remove();

                this.showCapture(x, y);
                this.messengers = this.messengers.filter(msg => msg.id !== id);
                this.emit('messageLost', { id, x, y });
                return;
            }

            if (m.progress >= 1) {
                this.state.messagesDelivered++;

                m.messenger.transition()
                    .duration(200)
                    .attr('transform', `translate(${m.endX}, ${startY}) scale(1.5)`)
                    .attr('opacity', 0)
                    .remove();

                this.messengers = this.messengers.filter(msg => msg.id !== id);
                this.showDelivery(m.endX, startY);
                this.emit('messageDelivered', { id });
                return;
            }

            requestAnimationFrame(animate);
        };

        requestAnimationFrame(animate);
    }

    /**
     * Show capture effect.
     */
    showCapture(x, y) {
        const effect = this.svg.append('g')
            .attr('transform', `translate(${x}, ${y})`);

        effect.append('text')
            .attr('text-anchor', 'middle')
            .attr('fill', this.colors.enemy)
            .attr('font-size', '12px')
            .attr('font-weight', 'bold')
            .text('CAPTURED!')
            .transition()
            .duration(1000)
            .attr('y', -30)
            .attr('opacity', 0)
            .remove();

        effect.append('text')
            .attr('text-anchor', 'middle')
            .attr('dy', 5)
            .attr('fill', this.colors.enemy)
            .attr('font-size', '20px')
            .text('X')
            .transition()
            .duration(500)
            .attr('opacity', 0)
            .remove();
    }

    /**
     * Show delivery effect.
     */
    showDelivery(x, y) {
        const effect = this.svg.append('g')
            .attr('transform', `translate(${x}, ${y})`);

        effect.append('circle')
            .attr('r', 5)
            .attr('fill', 'none')
            .attr('stroke', this.colors.alice)
            .attr('stroke-width', 2)
            .transition()
            .duration(500)
            .attr('r', 30)
            .attr('opacity', 0)
            .remove();
    }

    /**
     * Update the narrative text.
     */
    updateNarrative(text, subtext = '') {
        this.narrative.select('.narrative-text')
            .transition()
            .duration(300)
            .attr('opacity', 0)
            .transition()
            .duration(300)
            .text(text)
            .attr('opacity', 1);

        if (subtext) {
            this.narrative.select('.narrative-subtext')
                .transition()
                .duration(300)
                .attr('opacity', 0)
                .transition()
                .duration(300)
                .text(subtext)
                .attr('opacity', 1);
        }
    }

    /**
     * Start the dilemma demonstration.
     */
    startDemo(lossRate = 0.6) {
        this.isAnimating = true;
        let iteration = 0;

        const run = () => {
            if (!this.isAnimating) return;

            iteration++;
            const fromAlice = iteration % 2 === 1;
            this.sendMessenger(fromAlice, lossRate);

            if (this.state.messagesAttempted > 0 && this.state.messagesDelivered === 0) {
                this.updateNarrative(
                    'No messages are getting through! How can they coordinate?',
                    "Without reliable communication, coordination seems impossible..."
                );
            } else if (this.state.messagesDelivered > 0 && this.state.messagesDelivered < 3) {
                this.updateNarrative(
                    'A message arrived! But does the sender know it arrived?',
                    "The sender can't be sure unless they receive confirmation..."
                );
            }

            setTimeout(run, 1500);
        };

        run();
    }

    /**
     * Stop the animation.
     */
    stop() {
        this.isAnimating = false;
        if (this.animationFrame) {
            cancelAnimationFrame(this.animationFrame);
        }
    }

    /**
     * Reset the scene.
     */
    reset() {
        this.stop();
        this.state = {
            messagesAttempted: 0,
            messagesLost: 0,
            messagesDelivered: 0
        };
        this.messengers = [];
        this.messengerIdCounter = 0;
        this.init();
    }
}

/**
 * Create a standalone battlefield scene with controls.
 * @param {string} containerId - Container element ID
 * @returns {object} Scene instance and control methods
 */
export function createBattlefieldWithControls(containerId) {
    const container = document.getElementById(containerId);
    if (!container) return null;

    container.innerHTML = `
        <div class="battlefield-wrapper">
            <div id="${containerId}-scene"></div>
            <div class="battlefield-controls">
                <button id="${containerId}-start" class="primary">Start Demo</button>
                <button id="${containerId}-stop">Stop</button>
                <button id="${containerId}-reset">Reset</button>
            </div>
        </div>
    `;

    const scene = new BattlefieldScene(`#${containerId}-scene`);
    scene.init();

    document.getElementById(`${containerId}-start`)
        ?.addEventListener('click', () => scene.startDemo());
    document.getElementById(`${containerId}-stop`)
        ?.addEventListener('click', () => scene.stop());
    document.getElementById(`${containerId}-reset`)
        ?.addEventListener('click', () => scene.reset());

    return scene;
}
