/**
 * TGP Web Visualizer - 3D Battlefield with Homing Pigeons
 *
 * Three.js-powered 3D visualization showing:
 * - Two castles (Alice and Bob) on opposite sides
 * - Enemy fortress in the middle
 * - Homing pigeons carrying messages
 * - Intercepted messages (pigeons shot down, no gore)
 * - Beautiful 3D animations and camera work
 */

import * as THREE from 'three';
import { createAnimationControls } from './animation-controls.js';

export class Battlefield3D {
    constructor(containerSelector) {
        this.container = typeof containerSelector === 'string'
            ? document.querySelector(containerSelector)
            : containerSelector;

        if (!this.container) {
            console.error('Container not found:', containerSelector);
            return;
        }

        // Scene setup
        this.scene = null;
        this.camera = null;
        this.renderer = null;
        this.clock = new THREE.Clock();

        // Game objects
        this.aliceCastle = null;
        this.bobCastle = null;
        this.enemyCastle = null;
        this.pigeons = [];
        this.arrows = [];

        // Animation state
        this.speed = 1.0;
        this.isPaused = false;
        this.controls = null;
        this.animationId = null;

        // Stats
        this.stats = {
            sent: 0,
            intercepted: 0,
            delivered: 0
        };

        this.init();
    }

    init() {
        this.setupScene();
        this.setupLighting();
        this.createTerrain();
        this.createCastles();
        this.createAnimationControls();
        this.startAnimation();
    }

    setupScene() {
        // Create scene
        this.scene = new THREE.Scene();
        this.scene.background = new THREE.Color(0x87CEEB); // Sky blue
        this.scene.fog = new THREE.Fog(0x87CEEB, 50, 200);

        // Create camera
        const aspect = this.container.clientWidth / Math.max(this.container.clientHeight, 400);
        this.camera = new THREE.PerspectiveCamera(60, aspect, 0.1, 1000);
        this.camera.position.set(0, 35, 60);
        this.camera.lookAt(0, 0, 0);

        // Create renderer
        this.renderer = new THREE.WebGLRenderer({ antialias: true });
        this.renderer.setSize(this.container.clientWidth, Math.max(this.container.clientHeight, 400));
        this.renderer.shadowMap.enabled = true;
        this.renderer.shadowMap.type = THREE.PCFSoftShadowMap;
        this.container.appendChild(this.renderer.domElement);

        // Handle window resize
        window.addEventListener('resize', () => this.onWindowResize());
    }

    setupLighting() {
        // Ambient light
        const ambient = new THREE.AmbientLight(0xffffff, 0.6);
        this.scene.add(ambient);

        // Directional light (sun)
        const sun = new THREE.DirectionalLight(0xffffff, 0.8);
        sun.position.set(50, 50, 50);
        sun.castShadow = true;
        sun.shadow.camera.left = -50;
        sun.shadow.camera.right = 50;
        sun.shadow.camera.top = 50;
        sun.shadow.camera.bottom = -50;
        sun.shadow.mapSize.width = 2048;
        sun.shadow.mapSize.height = 2048;
        this.scene.add(sun);

        // Hemisphere light for better sky/ground gradient
        const hemiLight = new THREE.HemisphereLight(0x87CEEB, 0x3a5f0b, 0.4);
        this.scene.add(hemiLight);
    }

    createTerrain() {
        // Ground plane
        const groundGeometry = new THREE.PlaneGeometry(200, 80);
        const groundMaterial = new THREE.MeshStandardMaterial({
            color: 0x3a5f0b, // Dark green grass
            roughness: 0.8
        });
        const ground = new THREE.Mesh(groundGeometry, groundMaterial);
        ground.rotation.x = -Math.PI / 2;
        ground.receiveShadow = true;
        this.scene.add(ground);

        // Valley floor (darker strip in the middle for enemy territory)
        const valleyGeometry = new THREE.PlaneGeometry(200, 20);
        const valleyMaterial = new THREE.MeshStandardMaterial({
            color: 0x2a4505,
            roughness: 0.9
        });
        const valley = new THREE.Mesh(valleyGeometry, valleyMaterial);
        valley.rotation.x = -Math.PI / 2;
        valley.position.y = 0.01;
        valley.receiveShadow = true;
        this.scene.add(valley);
    }

    createCastles() {
        // Alice's Castle (left side, blue)
        this.aliceCastle = this.createCastle(-40, 0x58a6ff);
        this.scene.add(this.aliceCastle);

        // Bob's Castle (right side, green)
        this.bobCastle = this.createCastle(40, 0x3fb950);
        this.scene.add(this.bobCastle);

        // Enemy Castle (center, red)
        this.enemyCastle = this.createEnemyFortress();
        this.scene.add(this.enemyCastle);
    }

    createCastle(xPos, color) {
        const castle = new THREE.Group();

        // Main tower
        const towerGeometry = new THREE.CylinderGeometry(3, 4, 12, 8);
        const towerMaterial = new THREE.MeshStandardMaterial({ color, roughness: 0.7 });
        const tower = new THREE.Mesh(towerGeometry, towerMaterial);
        tower.position.y = 6;
        tower.castShadow = true;
        tower.receiveShadow = true;
        castle.add(tower);

        // Battlements
        for (let i = 0; i < 8; i++) {
            const angle = (i / 8) * Math.PI * 2;
            const bGeometry = new THREE.BoxGeometry(1, 1.5, 1);
            const battlement = new THREE.Mesh(bGeometry, towerMaterial);
            battlement.position.set(
                Math.cos(angle) * 3.5,
                12.75,
                Math.sin(angle) * 3.5
            );
            battlement.castShadow = true;
            castle.add(battlement);
        }

        // Roof/cone
        const roofGeometry = new THREE.ConeGeometry(3.5, 4, 8);
        const roofMaterial = new THREE.MeshStandardMaterial({ color: 0x8b4513, roughness: 0.8 });
        const roof = new THREE.Mesh(roofGeometry, roofMaterial);
        roof.position.y = 15;
        roof.castShadow = true;
        castle.add(roof);

        // Flag at top
        const flagPoleGeometry = new THREE.CylinderGeometry(0.1, 0.1, 3, 4);
        const flagPoleMaterial = new THREE.MeshStandardMaterial({ color: 0x654321 });
        const flagPole = new THREE.Mesh(flagPoleGeometry, flagPoleMaterial);
        flagPole.position.y = 18.5;
        castle.add(flagPole);

        castle.position.x = xPos;
        return castle;
    }

    createEnemyFortress() {
        const fortress = new THREE.Group();

        // Main wall
        const wallGeometry = new THREE.BoxGeometry(8, 8, 2);
        const wallMaterial = new THREE.MeshStandardMaterial({ color: 0x8b0000, roughness: 0.7 });
        const wall = new THREE.Mesh(wallGeometry, wallMaterial);
        wall.position.y = 4;
        wall.castShadow = true;
        wall.receiveShadow = true;
        fortress.add(wall);

        // Two guard towers
        for (let xOffset of [-5, 5]) {
            const towerGeometry = new THREE.CylinderGeometry(1.5, 2, 10, 6);
            const tower = new THREE.Mesh(towerGeometry, wallMaterial);
            tower.position.set(xOffset, 5, 0);
            tower.castShadow = true;
            fortress.add(tower);

            // Tower roof
            const roofGeometry = new THREE.ConeGeometry(2, 3, 6);
            const roofMaterial = new THREE.MeshStandardMaterial({ color: 0x2a0a0a });
            const roof = new THREE.Mesh(roofGeometry, roofMaterial);
            roof.position.set(xOffset, 11.5, 0);
            roof.castShadow = true;
            fortress.add(roof);
        }

        fortress.position.y = 0;
        return fortress;
    }

    createPigeon(fromAlice = true) {
        const pigeon = new THREE.Group();

        // Body (simplified, cute shape)
        const bodyGeometry = new THREE.SphereGeometry(0.4, 8, 8);
        bodyGeometry.scale(1, 0.8, 1.3);
        const bodyMaterial = new THREE.MeshStandardMaterial({ color: 0xcccccc });
        const body = new THREE.Mesh(bodyGeometry, bodyMaterial);
        pigeon.add(body);

        // Head
        const headGeometry = new THREE.SphereGeometry(0.25, 8, 8);
        const head = new THREE.Mesh(headGeometry, bodyMaterial);
        head.position.set(0, 0.2, 0.5);
        pigeon.add(head);

        // Beak
        const beakGeometry = new THREE.ConeGeometry(0.08, 0.2, 4);
        const beakMaterial = new THREE.MeshStandardMaterial({ color: 0xffaa00 });
        const beak = new THREE.Mesh(beakGeometry, beakMaterial);
        beak.rotation.x = Math.PI / 2;
        beak.position.set(0, 0.2, 0.7);
        pigeon.add(beak);

        // Wings (simple planes)
        const wingGeometry = new THREE.PlaneGeometry(0.6, 0.3);
        const wingMaterial = new THREE.MeshStandardMaterial({
            color: 0xaaaaaa,
            side: THREE.DoubleSide
        });

        const leftWing = new THREE.Mesh(wingGeometry, wingMaterial);
        leftWing.position.set(-0.5, 0, 0);
        leftWing.rotation.y = -Math.PI / 6;
        pigeon.add(leftWing);

        const rightWing = new THREE.Mesh(wingGeometry, wingMaterial);
        rightWing.position.set(0.5, 0, 0);
        rightWing.rotation.y = Math.PI / 6;
        pigeon.add(rightWing);

        // Message scroll (tiny cylinder)
        const scrollGeometry = new THREE.CylinderGeometry(0.05, 0.05, 0.3, 8);
        const scrollMaterial = new THREE.MeshStandardMaterial({ color: 0xf4e5c7 });
        const scroll = new THREE.Mesh(scrollGeometry, scrollMaterial);
        scroll.position.set(0, -0.3, 0.3);
        scroll.rotation.z = Math.PI / 2;
        pigeon.add(scroll);

        // Starting position
        const startX = fromAlice ? -40 : 40;
        const endX = fromAlice ? 40 : -40;

        pigeon.position.set(startX, 15, 0);
        pigeon.rotation.y = fromAlice ? 0 : Math.PI;

        // Animation state
        pigeon.userData = {
            fromAlice,
            startX,
            endX,
            progress: 0,
            speed: 0.003 + Math.random() * 0.002,
            altitude: 15 + Math.random() * 5,
            wingPhase: Math.random() * Math.PI * 2,
            leftWing,
            rightWing,
            isIntercepted: Math.random() < 0.3, // 30% interception rate
            interceptPoint: 0.4 + Math.random() * 0.2
        };

        this.scene.add(pigeon);
        this.pigeons.push(pigeon);
        this.stats.sent++;

        return pigeon;
    }

    animatePigeon(pigeon, deltaTime) {
        const data = pigeon.userData;
        if (data.destroyed) return;

        // Apply speed multiplier
        data.progress += data.speed * deltaTime * 60 * this.speed;

        // Wing flapping
        data.wingPhase += deltaTime * 10 * this.speed;
        const flapAngle = Math.sin(data.wingPhase) * 0.4;
        data.leftWing.rotation.z = -flapAngle;
        data.rightWing.rotation.z = flapAngle;

        // Linear interpolation across battlefield
        const t = data.progress;
        pigeon.position.x = data.startX + (data.endX - data.startX) * t;
        pigeon.position.y = data.altitude + Math.sin(t * Math.PI) * 3;

        // Check for interception
        if (data.isIntercepted && !data.hasBeenIntercepted && t >= data.interceptPoint) {
            this.interceptPigeon(pigeon);
            data.hasBeenIntercepted = true;
            this.stats.intercepted++;
            return;
        }

        // Check if delivered
        if (t >= 1.0 && !data.isIntercepted) {
            this.deliverPigeon(pigeon);
            data.destroyed = true;
            this.stats.delivered++;
        }
    }

    interceptPigeon(pigeon) {
        // Create arrow from enemy fortress
        const arrowGeometry = new THREE.CylinderGeometry(0.05, 0.05, 2, 4);
        const arrowMaterial = new THREE.MeshStandardMaterial({ color: 0x8b0000 });
        const arrow = new THREE.Mesh(arrowGeometry, arrowMaterial);

        arrow.position.copy(this.enemyCastle.position);
        arrow.position.y += 8;

        const direction = new THREE.Vector3();
        direction.subVectors(pigeon.position, arrow.position).normalize();
        arrow.lookAt(pigeon.position);
        arrow.rotation.x += Math.PI / 2;

        this.scene.add(arrow);

        arrow.userData = {
            velocity: direction.multiplyScalar(0.8),
            life: 0
        };
        this.arrows.push(arrow);

        // Pigeon falls (gentle, no gore)
        pigeon.userData.falling = true;
        pigeon.userData.fallVelocity = 0;
    }

    animateFallingPigeon(pigeon, deltaTime) {
        const data = pigeon.userData;
        data.fallVelocity += 9.8 * deltaTime * this.speed; // Gravity
        pigeon.position.y -= data.fallVelocity * deltaTime * this.speed;
        pigeon.rotation.x += deltaTime * 5 * this.speed; // Tumbling

        if (pigeon.position.y <= 0) {
            this.scene.remove(pigeon);
            data.destroyed = true;
        }
    }

    deliverPigeon(pigeon) {
        // Pigeon lands at destination castle
        // Create puff of smoke/celebration
        const particles = new THREE.Group();
        for (let i = 0; i < 10; i++) {
            const particleGeometry = new THREE.SphereGeometry(0.2, 4, 4);
            const particleMaterial = new THREE.MeshBasicMaterial({
                color: 0xffffff,
                transparent: true,
                opacity: 0.8
            });
            const particle = new THREE.Mesh(particleGeometry, particleMaterial);
            particle.position.set(
                (Math.random() - 0.5) * 2,
                (Math.random() - 0.5) * 2,
                (Math.random() - 0.5) * 2
            );
            particles.add(particle);
        }
        particles.position.copy(pigeon.position);
        this.scene.add(particles);

        setTimeout(() => this.scene.remove(particles), 500);
        this.scene.remove(pigeon);
    }

    createAnimationControls() {
        this.controls = createAnimationControls({
            container: this.container,
            defaultSpeed: 1.0,
            minSpeed: 0.25,
            maxSpeed: 3.0,
            step: 0.25,
            onSpeedChange: (speed) => {
                this.speed = speed;
            },
            onPlayPause: (isPlaying) => {
                this.isPaused = !isPlaying;
                if (isPlaying) {
                    // Send pigeons periodically when playing
                    this.startPigeonTimer();
                } else {
                    this.stopPigeonTimer();
                }
            },
            onReset: () => {
                this.reset();
            }
        });

        // Auto-start
        this.controls.setPlaying(true);
        this.startPigeonTimer();
    }

    startPigeonTimer() {
        if (this.pigeonTimer) return;

        this.pigeonTimer = setInterval(() => {
            if (!this.isPaused) {
                this.createPigeon(Math.random() < 0.5);
            }
        }, 2000 / this.speed);
    }

    stopPigeonTimer() {
        if (this.pigeonTimer) {
            clearInterval(this.pigeonTimer);
            this.pigeonTimer = null;
        }
    }

    startAnimation() {
        const animate = () => {
            this.animationId = requestAnimationFrame(animate);

            if (this.isPaused) return;

            const deltaTime = this.clock.getDelta();

            // Animate pigeons
            this.pigeons.forEach(pigeon => {
                if (pigeon.userData.falling) {
                    this.animateFallingPigeon(pigeon, deltaTime);
                } else if (!pigeon.userData.destroyed) {
                    this.animatePigeon(pigeon, deltaTime);
                }
            });

            // Animate arrows
            this.arrows.forEach((arrow, index) => {
                arrow.position.add(arrow.userData.velocity.clone().multiplyScalar(this.speed));
                arrow.userData.life += deltaTime * this.speed;

                if (arrow.userData.life > 2) {
                    this.scene.remove(arrow);
                    this.arrows.splice(index, 1);
                }
            });

            // Clean up destroyed pigeons
            this.pigeons = this.pigeons.filter(p => !p.userData.destroyed);

            // Gentle camera sway
            const time = this.clock.getElapsedTime();
            this.camera.position.x = Math.sin(time * 0.1) * 5;

            this.renderer.render(this.scene, this.camera);
        };

        animate();
    }

    reset() {
        // Remove all pigeons and arrows
        this.pigeons.forEach(p => this.scene.remove(p));
        this.arrows.forEach(a => this.scene.remove(a));
        this.pigeons = [];
        this.arrows = [];

        this.stats = {
            sent: 0,
            intercepted: 0,
            delivered: 0
        };

        this.clock.start();
    }

    onWindowResize() {
        if (!this.camera || !this.renderer) return;

        const width = this.container.clientWidth;
        const height = Math.max(this.container.clientHeight, 400);

        this.camera.aspect = width / height;
        this.camera.updateProjectionMatrix();
        this.renderer.setSize(width, height);
    }

    dispose() {
        this.stopPigeonTimer();
        if (this.animationId) {
            cancelAnimationFrame(this.animationId);
        }
        if (this.renderer) {
            this.renderer.dispose();
            this.container.removeChild(this.renderer.domElement);
        }
    }
}
