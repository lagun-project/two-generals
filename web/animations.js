/**
 * Animations and Visual Polish Module
 *
 * Provides:
 * - Scroll-triggered animations using Intersection Observer
 * - Loading states for async operations
 * - Smooth tab transition effects
 * - Helpful tooltips
 * - Micro-interactions for improved UX
 */

// =============================================================================
// Scroll-Triggered Animations
// =============================================================================

export class ScrollAnimationController {
    constructor() {
        this.observers = new Map();
        this.animatedElements = new Set();

        this.initIntersectionObserver();
        this.attachScrollAnimations();
    }

    initIntersectionObserver() {
        // Create observer for fade-in animations
        this.fadeInObserver = new IntersectionObserver(
            (entries) => this.handleFadeIntersection(entries),
            {
                threshold: 0.1,
                rootMargin: '0px 0px -100px 0px'
            }
        );

        // Create observer for slide-in animations
        this.slideInObserver = new IntersectionObserver(
            (entries) => this.handleSlideIntersection(entries),
            {
                threshold: 0.15,
                rootMargin: '0px 0px -50px 0px'
            }
        );

        // Create observer for number counters
        this.counterObserver = new IntersectionObserver(
            (entries) => this.handleCounterIntersection(entries),
            {
                threshold: 0.5
            }
        );
    }

    attachScrollAnimations() {
        // Attach fade-in to sections
        document.querySelectorAll('section').forEach(el => {
            el.classList.add('scroll-fade-in');
            el.style.opacity = '0';
            el.style.transform = 'translateY(20px)';
            el.style.transition = 'opacity 0.6s ease-out, transform 0.6s ease-out';
            this.fadeInObserver.observe(el);
        });

        // Attach slide-in to cards
        document.querySelectorAll('.hero-stat, .protocol-card, .impact-card, .theorem').forEach(el => {
            el.classList.add('scroll-slide-in');
            el.style.opacity = '0';
            el.style.transform = 'translateX(-30px)';
            el.style.transition = 'opacity 0.5s ease-out, transform 0.5s ease-out';
            this.slideInObserver.observe(el);
        });

        // Attach counter animations to number elements
        document.querySelectorAll('.hero-number, .lean-number, .stat-value').forEach(el => {
            if (el.textContent.match(/^\d+$/)) {
                el.dataset.targetValue = el.textContent;
                el.textContent = '0';
                this.counterObserver.observe(el);
            }
        });
    }

    handleFadeIntersection(entries) {
        entries.forEach(entry => {
            if (entry.isIntersecting && !this.animatedElements.has(entry.target)) {
                entry.target.style.opacity = '1';
                entry.target.style.transform = 'translateY(0)';
                this.animatedElements.add(entry.target);
                this.fadeInObserver.unobserve(entry.target);
            }
        });
    }

    handleSlideIntersection(entries) {
        entries.forEach((entry, index) => {
            if (entry.isIntersecting && !this.animatedElements.has(entry.target)) {
                // Stagger animation
                setTimeout(() => {
                    entry.target.style.opacity = '1';
                    entry.target.style.transform = 'translateX(0)';
                    this.animatedElements.add(entry.target);
                }, index * 50);
                this.slideInObserver.unobserve(entry.target);
            }
        });
    }

    handleCounterIntersection(entries) {
        entries.forEach(entry => {
            if (entry.isIntersecting && !this.animatedElements.has(entry.target)) {
                this.animateCounter(entry.target);
                this.animatedElements.add(entry.target);
                this.counterObserver.unobserve(entry.target);
            }
        });
    }

    animateCounter(element) {
        const target = parseInt(element.dataset.targetValue);
        const duration = 2000;
        const start = performance.now();
        const startValue = 0;

        const animate = (currentTime) => {
            const elapsed = currentTime - start;
            const progress = Math.min(elapsed / duration, 1);

            // Ease out cubic
            const easeProgress = 1 - Math.pow(1 - progress, 3);
            const currentValue = Math.floor(startValue + (target - startValue) * easeProgress);

            element.textContent = currentValue.toLocaleString();

            if (progress < 1) {
                requestAnimationFrame(animate);
            } else {
                element.textContent = target.toLocaleString();
            }
        };

        requestAnimationFrame(animate);
    }

    destroy() {
        this.fadeInObserver.disconnect();
        this.slideInObserver.disconnect();
        this.counterObserver.disconnect();
    }
}

// =============================================================================
// Loading States
// =============================================================================

export class LoadingStateManager {
    constructor() {
        this.activeLoaders = new Map();
    }

    /**
     * Show loading spinner for async operations
     */
    showLoading(elementId, message = 'Loading...') {
        const element = document.getElementById(elementId);
        if (!element) return;

        const loadingHtml = `
            <div class="loading-overlay" data-loader-id="${elementId}">
                <div class="loading-content">
                    <div class="loading-spinner"></div>
                    <div class="loading-message">${message}</div>
                </div>
            </div>
        `;

        // Add loading overlay
        element.style.position = 'relative';
        element.insertAdjacentHTML('beforeend', loadingHtml);

        this.activeLoaders.set(elementId, performance.now());
    }

    /**
     * Update loading message
     */
    updateLoading(elementId, message) {
        const loader = document.querySelector(`[data-loader-id="${elementId}"] .loading-message`);
        if (loader) {
            loader.textContent = message;
        }
    }

    /**
     * Hide loading with fade-out
     */
    hideLoading(elementId) {
        const loader = document.querySelector(`[data-loader-id="${elementId}"]`);
        if (!loader) return;

        // Fade out
        loader.style.opacity = '0';
        setTimeout(() => {
            loader.remove();
            this.activeLoaders.delete(elementId);
        }, 300);
    }

    /**
     * Show progress bar for long operations
     */
    showProgress(elementId, percent, message = '') {
        const element = document.getElementById(elementId);
        if (!element) return;

        let progressBar = element.querySelector('.progress-overlay');
        if (!progressBar) {
            const progressHtml = `
                <div class="progress-overlay" data-progress-id="${elementId}">
                    <div class="progress-bar-container">
                        <div class="progress-bar-fill"></div>
                    </div>
                    <div class="progress-message"></div>
                </div>
            `;
            element.style.position = 'relative';
            element.insertAdjacentHTML('beforeend', progressHtml);
            progressBar = element.querySelector('.progress-overlay');
        }

        const fill = progressBar.querySelector('.progress-bar-fill');
        const msg = progressBar.querySelector('.progress-message');

        fill.style.width = `${percent}%`;
        msg.textContent = message;
    }

    hideProgress(elementId) {
        const progress = document.querySelector(`[data-progress-id="${elementId}"]`);
        if (progress) {
            progress.style.opacity = '0';
            setTimeout(() => progress.remove(), 300);
        }
    }
}

// =============================================================================
// Tab Transition Effects
// =============================================================================

export class TabTransitionController {
    constructor() {
        this.currentTab = null;
        this.transitionDuration = 300;
    }

    /**
     * Animate tab transition with fade and slide
     */
    transitionToTab(fromPane, toPane, direction = 'forward') {
        if (!fromPane || !toPane) return;

        const slideDistance = 30;
        const slideDirection = direction === 'forward' ? slideDistance : -slideDistance;

        // Animate out
        fromPane.style.transition = `opacity ${this.transitionDuration}ms ease-out, transform ${this.transitionDuration}ms ease-out`;
        fromPane.style.opacity = '0';
        fromPane.style.transform = `translateX(${-slideDirection}px)`;

        setTimeout(() => {
            fromPane.classList.remove('active');
            fromPane.style.display = 'none';

            // Reset from pane
            fromPane.style.opacity = '';
            fromPane.style.transform = '';

            // Setup to pane
            toPane.style.display = 'block';
            toPane.style.opacity = '0';
            toPane.style.transform = `translateX(${slideDirection}px)`;

            // Trigger reflow
            toPane.offsetHeight;

            // Animate in
            toPane.style.transition = `opacity ${this.transitionDuration}ms ease-out, transform ${this.transitionDuration}ms ease-out`;
            toPane.classList.add('active');
            toPane.style.opacity = '1';
            toPane.style.transform = 'translateX(0)';
        }, this.transitionDuration);
    }

    /**
     * Add ripple effect to tab button
     */
    addRippleEffect(button, event) {
        const ripple = document.createElement('span');
        ripple.className = 'tab-ripple';

        const rect = button.getBoundingClientRect();
        const x = event.clientX - rect.left;
        const y = event.clientY - rect.top;

        ripple.style.left = `${x}px`;
        ripple.style.top = `${y}px`;

        button.appendChild(ripple);

        setTimeout(() => ripple.remove(), 600);
    }
}

// =============================================================================
// Tooltip System
// =============================================================================

export class TooltipManager {
    constructor() {
        this.activeTooltip = null;
        this.initTooltips();
    }

    initTooltips() {
        // Add tooltips to elements with data-tooltip attribute
        document.querySelectorAll('[data-tooltip]').forEach(el => {
            this.attachTooltip(el);
        });

        // Add helpful tooltips to interactive elements
        this.addContextualTooltips();
    }

    attachTooltip(element) {
        element.addEventListener('mouseenter', (e) => this.showTooltip(e.target));
        element.addEventListener('mouseleave', () => this.hideTooltip());
        element.addEventListener('focus', (e) => this.showTooltip(e.target));
        element.addEventListener('blur', () => this.hideTooltip());
    }

    showTooltip(element) {
        const text = element.getAttribute('data-tooltip');
        const position = element.getAttribute('data-tooltip-position') || 'top';

        if (!text) return;

        this.hideTooltip();

        const tooltip = document.createElement('div');
        tooltip.className = `tooltip tooltip-${position}`;
        tooltip.textContent = text;
        document.body.appendChild(tooltip);

        // Position tooltip
        const rect = element.getBoundingClientRect();
        const tooltipRect = tooltip.getBoundingClientRect();

        let top, left;

        switch (position) {
            case 'top':
                top = rect.top - tooltipRect.height - 8;
                left = rect.left + (rect.width - tooltipRect.width) / 2;
                break;
            case 'bottom':
                top = rect.bottom + 8;
                left = rect.left + (rect.width - tooltipRect.width) / 2;
                break;
            case 'left':
                top = rect.top + (rect.height - tooltipRect.height) / 2;
                left = rect.left - tooltipRect.width - 8;
                break;
            case 'right':
                top = rect.top + (rect.height - tooltipRect.height) / 2;
                left = rect.right + 8;
                break;
        }

        tooltip.style.top = `${top}px`;
        tooltip.style.left = `${left}px`;
        tooltip.style.opacity = '1';

        this.activeTooltip = tooltip;
    }

    hideTooltip() {
        if (this.activeTooltip) {
            this.activeTooltip.style.opacity = '0';
            setTimeout(() => {
                if (this.activeTooltip) {
                    this.activeTooltip.remove();
                    this.activeTooltip = null;
                }
            }, 200);
        }
    }

    addContextualTooltips() {
        // Add tooltips to loss preset buttons
        document.querySelectorAll('.loss-preset').forEach(btn => {
            const loss = btn.dataset.loss;
            btn.setAttribute('data-tooltip', `Set packet loss to ${loss}%`);
            btn.setAttribute('data-tooltip-position', 'bottom');
            this.attachTooltip(btn);
        });

        // Add tooltips to proof artifacts
        const proofDescriptions = {
            'commitment': 'Signed statement: "I will attack if you agree"',
            'double': 'Embeds both commitments (C_A and C_B)',
            'triple': 'Embeds both double proofs (D_A and D_B)',
            'quad': 'Epistemic fixpoint - mutual constructibility proven'
        };

        // Add tooltips to escalation bars
        document.querySelectorAll('.level').forEach(level => {
            const name = level.querySelector('.level-name')?.textContent;
            if (name) {
                level.setAttribute('data-tooltip', `${name} - Proof escalation level`);
                level.setAttribute('data-tooltip-position', 'right');
                this.attachTooltip(level);
            }
        });
    }
}

// =============================================================================
// Onboarding Overlay - REMOVED
// User preference: No fullscreen takeover UIs. Keep demos unobtrusive.
// See CLAUDE.md for guidelines.
// =============================================================================

// =============================================================================
// Micro-interactions
// =============================================================================

export class MicroInteractions {
    constructor() {
        this.initButtonEffects();
        this.initHoverEffects();
        this.initFocusEffects();
    }

    initButtonEffects() {
        document.querySelectorAll('button').forEach(button => {
            button.addEventListener('click', (e) => {
                this.createRipple(e);
                this.addPulseEffect(button);
            });
        });
    }

    createRipple(event) {
        const button = event.currentTarget;
        const ripple = document.createElement('span');
        ripple.className = 'button-ripple';

        const rect = button.getBoundingClientRect();
        const size = Math.max(rect.width, rect.height);
        const x = event.clientX - rect.left - size / 2;
        const y = event.clientY - rect.top - size / 2;

        ripple.style.width = ripple.style.height = `${size}px`;
        ripple.style.left = `${x}px`;
        ripple.style.top = `${y}px`;

        button.appendChild(ripple);
        setTimeout(() => ripple.remove(), 600);
    }

    addPulseEffect(element) {
        element.classList.add('button-pulse');
        setTimeout(() => element.classList.remove('button-pulse'), 300);
    }

    initHoverEffects() {
        // Add glow effect to cards on hover
        document.querySelectorAll('.protocol-card, .impact-card, .theorem').forEach(card => {
            card.addEventListener('mouseenter', () => {
                card.style.transition = 'transform 0.3s ease, box-shadow 0.3s ease';
                card.style.transform = 'translateY(-4px) scale(1.02)';
            });

            card.addEventListener('mouseleave', () => {
                card.style.transform = '';
            });
        });
    }

    initFocusEffects() {
        // Add visible focus effects
        document.querySelectorAll('button, a, input, select').forEach(el => {
            el.addEventListener('focus', () => {
                el.classList.add('has-focus');
            });

            el.addEventListener('blur', () => {
                el.classList.remove('has-focus');
            });
        });
    }
}

// =============================================================================
// Initialize All
// =============================================================================

export function initAnimations() {
    const scrollController = new ScrollAnimationController();
    const loadingManager = new LoadingStateManager();
    const tabController = new TabTransitionController();
    const tooltipManager = new TooltipManager();
    const microInteractions = new MicroInteractions();
    // REMOVED: Onboarding overlay - too intrusive, user preference is for non-blocking UX

    // Expose managers globally for use by other modules
    window.tgpAnimations = {
        scroll: scrollController,
        loading: loadingManager,
        tabs: tabController,
        tooltips: tooltipManager
    };

    return {
        scroll: scrollController,
        loading: loadingManager,
        tabs: tabController,
        tooltips: tooltipManager,
        microInteractions
    };
}
