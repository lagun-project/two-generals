/**
 * Animation Speed Controls - Reusable utility for all animations
 *
 * Provides:
 * - Speed slider (0.25x to 2x)
 * - Play/Pause toggle
 * - Reset button
 * - Step forward/backward (optional)
 */

/**
 * Create animation speed controls for a container.
 *
 * @param {Object} options - Configuration options
 * @param {HTMLElement} options.container - Container element to prepend controls to
 * @param {number} options.defaultSpeed - Default speed multiplier (default: 1.0)
 * @param {number} options.minSpeed - Minimum speed (default: 0.25)
 * @param {number} options.maxSpeed - Maximum speed (default: 2.0)
 * @param {number} options.step - Speed slider step (default: 0.25)
 * @param {Function} options.onSpeedChange - Callback when speed changes (speed) => void
 * @param {Function} options.onPlayPause - Callback when play/pause toggled (isPlaying) => void
 * @param {Function} options.onReset - Callback when reset clicked () => void
 * @param {Function} options.onStep - Optional callback for step forward/backward (direction) => void
 * @param {boolean} options.showStepControls - Show step forward/back buttons (default: false)
 * @returns {Object} - Control interface { setSpeed, setPlaying, destroy, element }
 */
export function createAnimationControls(options) {
    const {
        container,
        defaultSpeed = 1.0,
        minSpeed = 0.25,
        maxSpeed = 2.0,
        step = 0.25,
        onSpeedChange = () => {},
        onPlayPause = () => {},
        onReset = () => {},
        onStep = null,
        showStepControls = false
    } = options;

    let currentSpeed = defaultSpeed;
    let isPlaying = false;

    // Create controls container
    const controlsDiv = document.createElement('div');
    controlsDiv.className = 'animation-controls';

    // Speed slider section
    const sliderSection = document.createElement('div');
    sliderSection.className = 'speed-slider-container';

    const label = document.createElement('label');
    label.textContent = 'Speed:';
    sliderSection.appendChild(label);

    const slider = document.createElement('input');
    slider.type = 'range';
    slider.min = minSpeed;
    slider.max = maxSpeed;
    slider.step = step;
    slider.value = defaultSpeed;
    slider.setAttribute('aria-label', 'Animation speed');
    sliderSection.appendChild(slider);

    const speedValue = document.createElement('span');
    speedValue.className = 'speed-value';
    speedValue.textContent = `${defaultSpeed}x`;
    sliderSection.appendChild(speedValue);

    controlsDiv.appendChild(sliderSection);

    // Control buttons section
    const buttonsDiv = document.createElement('div');
    buttonsDiv.className = 'control-buttons';

    // Play/Pause button
    const playPauseBtn = document.createElement('button');
    playPauseBtn.className = 'play-pause-btn';
    playPauseBtn.innerHTML = '<span class="speed-icon">▶</span>Play';
    playPauseBtn.setAttribute('aria-label', 'Play animation');
    buttonsDiv.appendChild(playPauseBtn);

    // Reset button
    const resetBtn = document.createElement('button');
    resetBtn.className = 'reset-btn';
    resetBtn.innerHTML = '<span class="speed-icon">↻</span>Reset';
    resetBtn.setAttribute('aria-label', 'Reset animation');
    buttonsDiv.appendChild(resetBtn);

    // Step controls (optional)
    if (showStepControls && onStep) {
        const stepBackBtn = document.createElement('button');
        stepBackBtn.className = 'step-btn';
        stepBackBtn.innerHTML = '<span class="speed-icon">◄</span>Step Back';
        stepBackBtn.setAttribute('aria-label', 'Step backward');
        buttonsDiv.appendChild(stepBackBtn);

        const stepFwdBtn = document.createElement('button');
        stepFwdBtn.className = 'step-btn';
        stepFwdBtn.innerHTML = 'Step Fwd<span class="speed-icon">►</span>';
        stepFwdBtn.setAttribute('aria-label', 'Step forward');
        buttonsDiv.appendChild(stepFwdBtn);

        stepBackBtn.addEventListener('click', () => onStep(-1));
        stepFwdBtn.addEventListener('click', () => onStep(1));
    }

    controlsDiv.appendChild(buttonsDiv);

    // Event handlers
    slider.addEventListener('input', (e) => {
        currentSpeed = parseFloat(e.target.value);
        speedValue.textContent = `${currentSpeed}x`;
        onSpeedChange(currentSpeed);
    });

    playPauseBtn.addEventListener('click', () => {
        isPlaying = !isPlaying;
        playPauseBtn.innerHTML = isPlaying
            ? '<span class="speed-icon">⏸</span>Pause'
            : '<span class="speed-icon">▶</span>Play';
        playPauseBtn.setAttribute('aria-label', isPlaying ? 'Pause animation' : 'Play animation');

        if (isPlaying) {
            playPauseBtn.classList.add('active');
        } else {
            playPauseBtn.classList.remove('active');
        }

        onPlayPause(isPlaying);
    });

    resetBtn.addEventListener('click', () => {
        onReset();
    });

    // Insert at beginning of container
    if (container.firstChild) {
        container.insertBefore(controlsDiv, container.firstChild);
    } else {
        container.appendChild(controlsDiv);
    }

    // Public API
    return {
        element: controlsDiv,

        setSpeed(speed) {
            currentSpeed = speed;
            slider.value = speed;
            speedValue.textContent = `${speed}x`;
        },

        setPlaying(playing) {
            isPlaying = playing;
            playPauseBtn.innerHTML = playing
                ? '<span class="speed-icon">⏸</span>Pause'
                : '<span class="speed-icon">▶</span>Play';
            playPauseBtn.setAttribute('aria-label', playing ? 'Pause animation' : 'Play animation');

            if (playing) {
                playPauseBtn.classList.add('active');
            } else {
                playPauseBtn.classList.remove('active');
            }
        },

        getSpeed() {
            return currentSpeed;
        },

        isPlaying() {
            return isPlaying;
        },

        destroy() {
            controlsDiv.remove();
        }
    };
}
