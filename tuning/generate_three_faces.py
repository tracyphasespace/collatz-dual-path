#!/usr/bin/env python3
"""
Generate a 3-panel view showing each face with its distinct hole pattern:
- Front (blue): 2x3 holes
- Side (red): 4x5 holes
- Top (green): 6x7 holes
"""
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as patches

def draw_face_with_holes(ax, rows, cols, color, light_color, title):
    """Draw a square face with a grid of holes."""
    # Fill background
    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.set_aspect('equal')
    ax.add_patch(patches.Rectangle((0, 0), 1, 1, facecolor=color, edgecolor='black', linewidth=2))

    # Calculate hole positions and sizes
    margin = 0.08
    usable = 1 - 2 * margin

    hole_width = usable / (cols + 0.5)
    hole_height = usable / (rows + 0.5)
    hole_size_w = hole_width * 0.6
    hole_size_h = hole_height * 0.6

    # Draw holes
    for i in range(cols):
        for j in range(rows):
            x = margin + (i + 0.5) * hole_width + (hole_width - hole_size_w) / 2
            y = margin + (j + 0.5) * hole_height + (hole_height - hole_size_h) / 2
            # Dark hole with slight 3D effect
            ax.add_patch(patches.Rectangle(
                (x, y), hole_size_w, hole_size_h,
                facecolor='#1a1a2e', edgecolor='#0a0a1e', linewidth=1
            ))
            # Inner shadow
            ax.add_patch(patches.Rectangle(
                (x + 0.005, y + 0.005), hole_size_w - 0.01, hole_size_h - 0.01,
                facecolor='#0f0f1f', edgecolor='none'
            ))

    ax.set_title(title, fontsize=16, fontweight='bold', pad=10)
    ax.set_xticks([])
    ax.set_yticks([])
    for spine in ax.spines.values():
        spine.set_visible(False)

def main():
    fig, axes = plt.subplots(1, 3, figsize=(16, 6), facecolor='white')
    fig.suptitle('Three Faces with Different Hole Patterns', fontsize=20, fontweight='bold', y=1.02)

    # Front face - Blue - 2x3 holes
    draw_face_with_holes(axes[0], rows=3, cols=2,
                         color='#7090c0', light_color='#90b0e0',
                         title='Front Face (Blue)\n2 × 3 = 6 holes')

    # Side face - Red - 4x5 holes
    draw_face_with_holes(axes[1], rows=5, cols=4,
                         color='#c07070', light_color='#e09090',
                         title='Side Face (Red)\n4 × 5 = 20 holes')

    # Top face - Green - 6x7 holes
    draw_face_with_holes(axes[2], rows=7, cols=6,
                         color='#70c070', light_color='#90e090',
                         title='Top Face (Green)\n6 × 7 = 42 holes')

    plt.tight_layout()

    output_path = '/home/tracy/development/Riemann/tuning/three_faces_holes.png'
    plt.savefig(output_path, dpi=200, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    print(f"Saved to: {output_path}")
    plt.close()

if __name__ == "__main__":
    main()
