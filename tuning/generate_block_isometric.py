#!/usr/bin/env python3
"""
Rectangular block with prime hole patterns evenly spaced on each face:
- Front: 2×13 = 26 holes
- Side: 3×11 = 33 holes
- Top: 5×7 = 35 holes

Holes are evenly distributed regardless of block dimensions.
"""
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
from matplotlib.collections import LineCollection

def iso(x, y, z):
    """Isometric projection - viewing front faces."""
    # Flip Z so we see front-left corner instead of back-right
    return (x * 0.866 - z * 0.866, y + x * 0.25 + z * 0.25)

def draw_face_with_grid(ax, corners_3d, face_color, holes_cols, holes_rows,
                         grid_color, hole_color, zorder=1):
    """Draw a face with grid lines and evenly spaced holes."""
    corners_2d = [iso(*c) for c in corners_3d]

    face = Polygon(corners_2d, facecolor=face_color, edgecolor='#333333',
                   linewidth=2, zorder=zorder)
    ax.add_patch(face)

    v1 = np.array(corners_3d[1]) - np.array(corners_3d[0])
    v2 = np.array(corners_3d[3]) - np.array(corners_3d[0])
    origin = np.array(corners_3d[0])

    # Grid lines showing the hole spacing
    grid_lines = []
    for i in range(holes_cols + 1):
        u = i / holes_cols
        p1 = origin + u * v1
        p2 = origin + u * v1 + v2
        grid_lines.append([iso(*p1), iso(*p2)])
    for j in range(holes_rows + 1):
        v = j / holes_rows
        p1 = origin + v * v2
        p2 = origin + v1 + v * v2
        grid_lines.append([iso(*p1), iso(*p2)])

    lc = LineCollection(grid_lines, colors=grid_color, linewidths=0.6, zorder=zorder+0.3)
    ax.add_collection(lc)

    # Holes centered in each cell
    hole_margin = 0.18

    for i in range(holes_cols):
        for j in range(holes_rows):
            u_start = i / holes_cols
            u_end = (i + 1) / holes_cols
            v_start = j / holes_rows
            v_end = (j + 1) / holes_rows

            hu_start = u_start + (u_end - u_start) * hole_margin
            hu_end = u_end - (u_end - u_start) * hole_margin
            hv_start = v_start + (v_end - v_start) * hole_margin
            hv_end = v_end - (v_end - v_start) * hole_margin

            hole_corners_3d = [
                origin + hu_start * v1 + hv_start * v2,
                origin + hu_end * v1 + hv_start * v2,
                origin + hu_end * v1 + hv_end * v2,
                origin + hu_start * v1 + hv_end * v2,
            ]

            hole_corners_2d = [iso(*c) for c in hole_corners_3d]
            hole = Polygon(hole_corners_2d, facecolor=hole_color,
                          edgecolor='#222222', linewidth=0.3, zorder=zorder+0.5)
            ax.add_patch(hole)

def main():
    fig, ax = plt.subplots(figsize=(16, 12), facecolor='white')

    # Block proportions chosen for visual appeal
    W, H, D = 8.0, 10.0, 9.0

    c = {
        'fbl': (0, 0, 0),
        'fbr': (W, 0, 0),
        'ftl': (0, H, 0),
        'ftr': (W, H, 0),
        'bbl': (0, 0, D),
        'bbr': (W, 0, D),
        'btl': (0, H, D),
        'btr': (W, H, D),
    }

    # Grayscale palette
    gray1 = '#f0f0f0'    # Lightest - top
    gray2 = '#d8d8d8'    # Medium - front
    gray3 = '#c0c0c0'    # Darker - side
    grid_color = '#999999'
    hole_color = '#404040'

    # Top: 5×7 = 35 holes (primes) - top face visible from above
    top = [c['ftl'], c['ftr'], c['btr'], c['btl']]
    draw_face_with_grid(ax, top, gray1, 5, 7, grid_color, hole_color, zorder=10)

    # Left side: 3×11 = 33 holes (primes) - left face now visible
    left = [c['bbl'], c['fbl'], c['ftl'], c['btl']]
    draw_face_with_grid(ax, left, gray3, 3, 11, grid_color, hole_color, zorder=20)

    # Front: 2×13 = 26 holes (primes) - front face
    front = [c['fbl'], c['fbr'], c['ftr'], c['ftl']]
    draw_face_with_grid(ax, front, gray2, 2, 13, grid_color, hole_color, zorder=30)

    ax.set_aspect('equal')
    ax.autoscale()
    ax.margins(0.08)
    ax.axis('off')

    ax.set_title('Rectangular Block with Prime Hole Patterns\n' +
                 'Front: 2×13 = 26  |  Left: 3×11 = 33  |  Top: 5×7 = 35',
                 fontsize=18, fontweight='bold', pad=20)

    plt.tight_layout()

    output_path = '/home/tracy/development/Riemann/tuning/block_primes.png'
    plt.savefig(output_path, dpi=200, bbox_inches='tight', facecolor='white')
    print(f"Saved to: {output_path}")
    plt.close()

if __name__ == "__main__":
    main()
