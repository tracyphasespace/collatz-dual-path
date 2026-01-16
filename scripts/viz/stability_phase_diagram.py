#!/usr/bin/env python3
"""
Stability Phase Diagram for the Riemann Hypothesis

Visualizes the critical line Re(s) = 1/2 as a phase boundary between:
- Expansive Phase (sigma > 1/2): Sieve tunnels widen exponentially
- Contractive Phase (sigma < 1/2): Prime dust collapses

This figure makes Lemma 5.1 (Stability Theorem) visually intuitive.
"""

from datetime import datetime

import matplotlib.pyplot as plt
import numpy as np
from matplotlib.patches import FancyArrowPatch
from matplotlib.colors import LinearSegmentedColormap


def stability_phase_diagram(output=None):
    """
    Creates the Stability Phase Diagram showing why zeros must lie on Re(s)=1/2.
    """
    fig, ax = plt.subplots(figsize=(12, 8))

    # Parameters
    sigma = np.linspace(0, 1, 500)
    t = np.linspace(0, 50, 500)
    SIGMA, T = np.meshgrid(sigma, t)

    # --- PHASE REGIONS ---
    # The "geometric volume" or sieve density as a function of sigma
    # Left of critical line: contractive (volume shrinks)
    # Right of critical line: expansive (volume grows)
    # Critical line: unitary (volume preserved)

    # Create phase field: deviation from critical line determines instability
    phase_field = np.abs(SIGMA - 0.5)

    # Color the regions (CORRECTED per analytic number theory):
    # σ < 1/2 (Left): EXPANSIVE - terms p^(-s) grow, tunnel widens → RED (unstable/hot)
    # σ > 1/2 (Right): CONTRACTIVE - terms p^(-s) shrink, dust collapses → BLUE (stable/cold)
    left_mask = SIGMA < 0.5
    right_mask = SIGMA > 0.5

    # Create custom diverging colormap (red-white-blue)
    # Red on left (expansive/unstable), Blue on right (contractive/stable)
    colors_left = plt.cm.Reds_r(np.linspace(0.3, 0.9, 128))
    colors_right = plt.cm.Blues(np.linspace(0.3, 0.9, 128))
    all_colors = np.vstack([colors_left, colors_right])
    cmap = LinearSegmentedColormap.from_list('phase', all_colors)

    # Plot the phase field
    phase_plot = (SIGMA - 0.5)  # Negative on left (expansive), positive on right (contractive)
    im = ax.imshow(phase_plot, extent=[0, 1, 0, 50], origin='lower',
                   aspect='auto', cmap=cmap, alpha=0.7, vmin=-0.5, vmax=0.5)

    # --- THE CRITICAL LINE ---
    ax.axvline(x=0.5, color='gold', linewidth=4, linestyle='-',
               label=r'Critical Line $\sigma = 1/2$', zorder=10)
    # Add glow effect
    for width, alpha in [(8, 0.1), (6, 0.15), (4, 0.2)]:
        ax.axvline(x=0.5, color='yellow', linewidth=width, alpha=alpha, zorder=9)

    # --- WAVE BEHAVIOR OVERLAY ---
    # Show exploding wave on left (expansive), damped wave on right (contractive)
    t_wave = np.linspace(5, 45, 200)

    # Left side: Exploding oscillation (EXPANSIVE - σ < 1/2)
    sigma_left = 0.25
    amplitude_left = 0.03 * np.exp(0.02 * (t_wave - 25))  # Exponential growth
    amplitude_left = np.clip(amplitude_left, 0, 0.15)  # Clip for visibility
    wave_left = sigma_left + amplitude_left * np.sin(0.5 * t_wave)
    ax.plot(wave_left, t_wave, color='darkred', linewidth=2, alpha=0.8)

    # Right side: Damped oscillation (CONTRACTIVE - σ > 1/2)
    sigma_right = 0.75
    amplitude_right = 0.08 * np.exp(-0.05 * (t_wave - 25)**2 / 50)  # Gaussian decay
    wave_right = sigma_right + amplitude_right * np.sin(0.5 * t_wave)
    ax.plot(wave_right, t_wave, color='navy', linewidth=2, alpha=0.8)

    # Center: Stable oscillation (unitary)
    sigma_center = 0.5
    amplitude_center = 0.03  # Constant amplitude
    wave_center = sigma_center + amplitude_center * np.sin(0.5 * t_wave)
    ax.plot(wave_center, t_wave, color='gold', linewidth=3, alpha=0.9, zorder=11)

    # --- ZETA ZEROS ---
    # Plot first few known zeros on the critical line
    zeros_t = [14.13, 21.02, 25.01, 30.42, 32.94, 37.59, 40.92, 43.33, 48.01]
    for zt in zeros_t:
        if zt < 50:
            ax.scatter([0.5], [zt], color='lime', s=80, zorder=15,
                      edgecolors='darkgreen', linewidth=1.5)

    # --- ANNOTATIONS ---
    # Phase labels (CORRECTED: Left=Expansive, Right=Contractive)
    ax.text(0.15, 45, 'EXPANSIVE\nPHASE', fontsize=14, fontweight='bold',
            color='darkred', ha='center', va='top',
            bbox=dict(boxstyle='round', facecolor='white', alpha=0.8))
    ax.text(0.15, 38, r'$\|K(s)\| > 1$' + '\nTunnel Widens', fontsize=10,
            color='darkred', ha='center', va='top')

    ax.text(0.85, 45, 'CONTRACTIVE\nPHASE', fontsize=14, fontweight='bold',
            color='navy', ha='center', va='top',
            bbox=dict(boxstyle='round', facecolor='white', alpha=0.8))
    ax.text(0.85, 38, r'$\|K(s)\| < 1$' + '\nDust Collapses', fontsize=10,
            color='darkblue', ha='center', va='top')

    # Stability explanation
    ax.text(0.5, -5, r'$K(s)^{\dagger} = K(s)$ only when $\mathrm{Re}(s) = 1/2$',
            fontsize=11, ha='center', va='top', style='italic',
            transform=ax.transData)

    # Arrow annotations for wave behavior (CORRECTED)
    ax.annotate('Exploding\n(Diverges)', xy=(0.18, 25), fontsize=9, color='darkred',
                ha='center', va='center')
    ax.annotate('Stable\n(Preserved)', xy=(0.58, 25), fontsize=9, color='gold',
                ha='left', va='center', fontweight='bold')
    ax.annotate('Damped\n(Decays)', xy=(0.82, 25), fontsize=9, color='navy',
                ha='center', va='center')

    # Zeros annotation
    ax.annotate('Zeta Zeros\n(Forced here)', xy=(0.5, 14.13), xytext=(0.65, 10),
                fontsize=10, color='darkgreen', ha='left',
                arrowprops=dict(arrowstyle='->', color='green', lw=1.5))

    # --- STYLING ---
    ax.set_xlim(0, 1)
    ax.set_ylim(0, 50)
    ax.set_xlabel(r'Real Part $\sigma = \mathrm{Re}(s)$', fontsize=12)
    ax.set_ylabel(r'Imaginary Part $t = \mathrm{Im}(s)$', fontsize=12)
    ax.set_title('Stability Phase Diagram: The Critical Line as Phase Boundary',
                 fontsize=14, fontweight='bold', pad=20)

    # Add colorbar (CORRECTED labels)
    cbar = plt.colorbar(im, ax=ax, shrink=0.6, pad=0.02)
    cbar.set_label('Phase Parameter\n' + r'$(\sigma - 1/2)$', fontsize=10)
    cbar.set_ticks([-0.4, -0.2, 0, 0.2, 0.4])
    cbar.set_ticklabels(['Expansive', '', 'Unitary', '', 'Contractive'])

    # Critical strip boundaries
    ax.axvline(x=0, color='gray', linewidth=1, linestyle=':', alpha=0.5)
    ax.axvline(x=1, color='gray', linewidth=1, linestyle=':', alpha=0.5)
    ax.text(0.02, 2, r'$\sigma=0$', fontsize=9, color='gray')
    ax.text(0.92, 2, r'$\sigma=1$', fontsize=9, color='gray')

    plt.tight_layout()

    if output:
        fig.savefig(output, dpi=300, bbox_inches='tight', facecolor='white')
        print(f"Wrote Stability Phase Diagram to {output}")
        plt.close(fig)
    else:
        plt.show()


if __name__ == "__main__":
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    stability_phase_diagram(
        output=f"tuning/stability_phase_diagram_{timestamp}.png"
    )
