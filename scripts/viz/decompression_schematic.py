#!/usr/bin/env python3
"""
Decompression Schematic: Complex Plane vs Clifford Algebra

Visualizes the "algebraic lift" from C to Cl(3,3):
- Panel A: Standard complex plane with entangled rotation/dilation
- Panel B: Clifford algebra with separated degrees of freedom

This figure illustrates the "Representational Inadequacy" argument in Section 2.
"""

from datetime import datetime

import matplotlib.pyplot as plt
import numpy as np
from mpl_toolkits.mplot3d import Axes3D
from matplotlib.patches import FancyArrowPatch, Circle, Arc
from matplotlib.lines import Line2D
import matplotlib.patches as mpatches


def decompression_schematic(output=None):
    """
    Creates a two-panel comparison of compressed vs unfolded geometry.
    """
    fig = plt.figure(figsize=(16, 7))

    # =========================================================================
    # PANEL A: THE COMPLEX PLANE (Compressed / Ambiguous)
    # =========================================================================
    ax1 = fig.add_subplot(121)
    ax1.set_aspect('equal')

    # Draw coordinate axes
    ax1.axhline(y=0, color='gray', linewidth=0.8, alpha=0.5)
    ax1.axvline(x=0, color='gray', linewidth=0.8, alpha=0.5)

    # The complex number z = x + iy
    z_x, z_y = 2.5, 2.0
    z_mag = np.sqrt(z_x**2 + z_y**2)
    z_angle = np.arctan2(z_y, z_x)

    # Draw the vector z
    ax1.annotate('', xy=(z_x, z_y), xytext=(0, 0),
                arrowprops=dict(arrowstyle='->', color='purple', lw=2.5))
    ax1.plot(z_x, z_y, 'o', color='purple', markersize=10, zorder=10)
    ax1.text(z_x + 0.2, z_y + 0.2, r'$z = x + iy$', fontsize=14, color='purple',
             fontweight='bold')

    # Show magnitude (dilation)
    ax1.annotate('', xy=(z_mag * 0.6, 0), xytext=(0, 0),
                arrowprops=dict(arrowstyle='<->', color='red', lw=1.5))
    ax1.text(z_mag * 0.3, -0.4, r'$|z|$ (Dilation)', fontsize=11, color='red',
             ha='center')

    # Show angle (rotation) - draw arc
    arc_radius = 1.0
    theta_arc = np.linspace(0, z_angle, 50)
    ax1.plot(arc_radius * np.cos(theta_arc), arc_radius * np.sin(theta_arc),
             color='blue', linewidth=2)
    ax1.text(1.3, 0.5, r'$\theta$ (Rotation)', fontsize=11, color='blue')

    # The problematic single 'i'
    ax1.text(-0.3, 2.8, r'$i = \sqrt{-1}$', fontsize=14, color='darkgreen',
             bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.9))
    ax1.annotate('', xy=(0, 2.5), xytext=(0, 2.0),
                arrowprops=dict(arrowstyle='->', color='darkgreen', lw=2))
    ax1.text(0.6, 2.3, 'Encodes BOTH\nRotation & Dilation', fontsize=10,
             color='darkgreen', style='italic', ha='left')

    # Entanglement visualization: dotted lines showing coupling
    ax1.plot([0, z_x], [0, 0], '--', color='red', alpha=0.5, linewidth=1)
    ax1.plot([z_x, z_x], [0, z_y], '--', color='blue', alpha=0.5, linewidth=1)

    # Warning box
    ax1.text(0.5, -1.8, 'ENTANGLED DEGREES OF FREEDOM',
             fontsize=11, color='darkred', fontweight='bold', ha='center',
             bbox=dict(boxstyle='round', facecolor='mistyrose', edgecolor='red'))

    ax1.set_xlim(-1.5, 4)
    ax1.set_ylim(-2.5, 3.5)
    ax1.set_xlabel('Real Axis', fontsize=12)
    ax1.set_ylabel('Imaginary Axis', fontsize=12)
    ax1.set_title('Panel A: Standard Complex Plane\n(Compressed / Ambiguous Dynamics)',
                  fontsize=13, fontweight='bold', pad=10)
    ax1.grid(True, alpha=0.2)

    # =========================================================================
    # PANEL B: CLIFFORD ALGEBRA Cl(3,3) (Unfolded / Independent)
    # =========================================================================
    ax2 = fig.add_subplot(122, projection='3d')

    # Set up 3D view
    ax2.view_init(elev=20, azim=45)

    # Coordinate system
    ax_len = 3
    ax2.plot([0, ax_len], [0, 0], [0, 0], 'k-', alpha=0.3, linewidth=1)
    ax2.plot([0, 0], [0, ax_len], [0, 0], 'k-', alpha=0.3, linewidth=1)
    ax2.plot([0, 0], [0, 0], [0, ax_len], 'k-', alpha=0.3, linewidth=1)

    # Labels for axes
    ax2.text(ax_len + 0.3, 0, 0, r'$e_1$', fontsize=11, color='gray')
    ax2.text(0, ax_len + 0.3, 0, r'$e_2$', fontsize=11, color='gray')
    ax2.text(0, 0, ax_len + 0.3, r'$e_3$ (Scalar/Dilation)', fontsize=11, color='red')

    # ROTATION: Draw a circular path in the e1-e2 plane (bivector plane)
    theta = np.linspace(0, 2*np.pi, 100)
    radius = 1.5
    circle_x = radius * np.cos(theta)
    circle_y = radius * np.sin(theta)
    circle_z = np.zeros_like(theta)
    ax2.plot(circle_x, circle_y, circle_z, color='blue', linewidth=2.5,
             label='Rotation (Bivector Plane)')

    # Arrow indicating rotation direction
    idx = 25
    ax2.quiver(circle_x[idx], circle_y[idx], 0,
               circle_x[idx+1] - circle_x[idx],
               circle_y[idx+1] - circle_y[idx], 0,
               color='blue', arrow_length_ratio=0.3, linewidth=2)
    ax2.text(2, 1.5, 0.2, r'$e_{12}$ Rotation', fontsize=11, color='blue',
             fontweight='bold')

    # DILATION: Draw a vertical arrow along e3 axis
    dilation_start = 0.5
    dilation_end = 2.5
    ax2.quiver(0, 0, dilation_start, 0, 0, dilation_end - dilation_start,
               color='red', arrow_length_ratio=0.15, linewidth=3)
    ax2.text(0.3, 0.3, 2.0, r'$\sigma$ Dilation', fontsize=11, color='red',
             fontweight='bold')

    # The vector in the unfolded space
    # Position it above the rotation plane to show separation
    v_x, v_y, v_z = 1.5, 1.0, 1.8
    ax2.scatter([v_x], [v_y], [v_z], color='purple', s=100, zorder=10)
    ax2.plot([0, v_x], [0, v_y], [0, v_z], color='purple', linewidth=2, alpha=0.7)
    ax2.text(v_x + 0.2, v_y + 0.2, v_z + 0.2,
             r'$S = e^{\sigma e_3} R_{12}$', fontsize=12, color='purple',
             fontweight='bold')

    # Show projection lines to emphasize separation
    ax2.plot([v_x, v_x], [v_y, v_y], [0, v_z], '--', color='red', alpha=0.5, linewidth=1)
    ax2.plot([0, v_x], [0, v_y], [0, 0], '--', color='blue', alpha=0.5, linewidth=1)

    # Bivector plane shading
    xx, yy = np.meshgrid(np.linspace(-2, 2, 10), np.linspace(-2, 2, 10))
    zz = np.zeros_like(xx)
    ax2.plot_surface(xx, yy, zz, alpha=0.1, color='blue')
    ax2.text(-1.5, -1.5, 0.1, 'Bivector Plane\n' + r'$(e_1 \wedge e_2)$',
             fontsize=10, color='darkblue', ha='center')

    # Independence annotation
    ax2.text2D(0.5, 0.02, 'ORTHOGONAL DEGREES OF FREEDOM',
               transform=ax2.transAxes, fontsize=11, color='darkgreen',
               fontweight='bold', ha='center',
               bbox=dict(boxstyle='round', facecolor='honeydew', edgecolor='green'))

    ax2.set_xlim(-2.5, 3)
    ax2.set_ylim(-2.5, 3)
    ax2.set_zlim(0, 3)
    ax2.set_xlabel(r'$e_1$', fontsize=11)
    ax2.set_ylabel(r'$e_2$', fontsize=11)
    ax2.set_zlabel('Scalar Axis', fontsize=11)
    ax2.set_title('Panel B: Clifford Algebra Cl(3,3)\n(Unfolded / Independent Dynamics)',
                  fontsize=13, fontweight='bold', pad=10)

    # =========================================================================
    # OVERALL STYLING
    # =========================================================================

    # Add connecting arrow/text between panels
    fig.text(0.5, 0.02,
             r'ALGEBRAIC LIFT: $\mathbb{C} \hookrightarrow Cl(3,3)$' +
             '\nRotation and Dilation become geometrically orthogonal',
             ha='center', fontsize=12, style='italic',
             bbox=dict(boxstyle='round', facecolor='lightyellow', alpha=0.9))

    # Add legend for Panel B
    legend_elements = [
        Line2D([0], [0], color='blue', linewidth=2, label='Rotation (Phase)'),
        Line2D([0], [0], color='red', linewidth=2, label='Dilation (Scale)'),
        Line2D([0], [0], marker='o', color='w', markerfacecolor='purple',
               markersize=10, label='Spinor Element')
    ]
    ax2.legend(handles=legend_elements, loc='upper left', fontsize=9)

    plt.tight_layout(rect=[0, 0.08, 1, 1])

    if output:
        fig.savefig(output, dpi=300, bbox_inches='tight', facecolor='white')
        print(f"Wrote Decompression Schematic to {output}")
        plt.close(fig)
    else:
        plt.show()


if __name__ == "__main__":
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    decompression_schematic(
        output=f"tuning/decompression_schematic_{timestamp}.png"
    )
