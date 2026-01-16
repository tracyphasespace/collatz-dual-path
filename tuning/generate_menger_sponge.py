#!/usr/bin/env python3
"""
Generate a four-panel Menger Sponge visualization showing iterations 0-3.
"""
import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D

def menger_sponge(level, size=1):
    """
    Generate a 3D boolean array representing a Menger Sponge at given iteration level.
    Returns array of shape (3^level, 3^level, 3^level) where True = solid.
    """
    if level == 0:
        return np.ones((1, 1, 1), dtype=bool)

    n = 3 ** level
    sponge = np.zeros((n, n, n), dtype=bool)

    # Get the previous level sponge
    prev = menger_sponge(level - 1)
    prev_size = prev.shape[0]

    # Place 20 copies (exclude center and face centers)
    for x in range(3):
        for y in range(3):
            for z in range(3):
                # Count how many coordinates are 1 (center position)
                center_count = (x == 1) + (y == 1) + (z == 1)
                # Keep if at most 1 coordinate is centered (removes center + 6 face centers)
                if center_count < 2:
                    x_start = x * prev_size
                    y_start = y * prev_size
                    z_start = z * prev_size
                    sponge[x_start:x_start+prev_size,
                           y_start:y_start+prev_size,
                           z_start:z_start+prev_size] = prev

    return sponge

def plot_menger(ax, level, title):
    """Plot a single Menger Sponge on given axes."""
    sponge = menger_sponge(level)

    # Create color array - gradient based on position for depth perception
    n = sponge.shape[0]
    colors = np.empty(sponge.shape + (4,), dtype=np.float32)

    # Create a lighter blue-purple gradient
    for i in range(n):
        for j in range(n):
            for k in range(n):
                if sponge[i, j, k]:
                    # Color based on position for 3D effect - brighter palette
                    r = 0.55 + 0.30 * (i / max(n-1, 1))
                    g = 0.55 + 0.25 * (j / max(n-1, 1))
                    b = 0.72 + 0.23 * (k / max(n-1, 1))
                    colors[i, j, k] = [r, g, b, 1.0]

    ax.voxels(sponge, facecolors=colors, edgecolor='#6a6a8e', linewidth=0.1)
    ax.set_title(title, fontsize=14, fontweight='bold', pad=10)

    # Clean up axes
    ax.set_xticks([])
    ax.set_yticks([])
    ax.set_zticks([])
    ax.set_box_aspect([1, 1, 1])

    # Set viewing angle
    ax.view_init(elev=20, azim=45)

def main():
    # Create figure with 2x2 subplots
    fig = plt.figure(figsize=(14, 14), facecolor='white')
    fig.suptitle('Menger Sponge: Fractal Iterations 0-3',
                 fontsize=20, fontweight='bold', y=0.95)

    panels = [
        (0, 'Level 0: Solid Cube\n(1 cube)'),
        (1, 'Level 1: First Iteration\n(20 cubes)'),
        (2, 'Level 2: Second Iteration\n(400 cubes)'),
        (3, 'Level 3: Third Iteration\n(8,000 cubes)')
    ]

    for idx, (level, title) in enumerate(panels):
        ax = fig.add_subplot(2, 2, idx + 1, projection='3d')
        ax.set_facecolor('white')
        print(f"Generating level {level}...")
        plot_menger(ax, level, title)

    plt.tight_layout(rect=[0, 0.02, 1, 0.93])

    # Save the figure
    output_path = '/home/tracy/development/Riemann/tuning/menger_sponge_4panel.png'
    plt.savefig(output_path, dpi=200, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    print(f"Saved to: {output_path}")

    plt.close()

if __name__ == "__main__":
    main()
