#!/usr/bin/env python3
"""
Generate a custom 3D cube with different hole patterns on each face:
- Front (blue): 2x3 holes
- Right side (red): 4x5 holes
- Top (green): 6x7 holes
"""
import numpy as np
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D

def create_custom_cube():
    """
    Create a 3D voxel array with different hole patterns on each face.
    We use a resolution that accommodates all patterns.
    """
    # Use LCM-friendly resolution: 42 x 42 x 42 (divisible by 2,3,4,5,6,7)
    n = 42
    cube = np.ones((n, n, n), dtype=bool)

    # Front face (Z = max, looking at XY plane): 2x3 = 6 holes (blue face)
    # Holes go through in Z direction
    hole_width_x = n // 3  # 3 columns
    hole_width_y = n // 4  # 4 rows (for 3 holes vertically, need 4 divisions)
    for i in range(2):  # 2 holes horizontally
        for j in range(3):  # 3 holes vertically
            x_start = hole_width_x * (i + 1) - hole_width_x // 2 - hole_width_x // 4
            x_end = x_start + hole_width_x // 2
            y_start = hole_width_y * (j + 1) - hole_width_y // 2 - hole_width_y // 4
            y_end = y_start + hole_width_y // 2
            x_start = max(0, int(n * (i + 0.5) / 3))
            x_end = int(n * (i + 1) / 3)
            y_start = int(n * j / 3)
            y_end = int(n * (j + 1) / 3)
            # Punch through
            cube[x_start:x_end, y_start:y_end, :] = False

    # Reset and do it properly
    cube = np.ones((n, n, n), dtype=bool)

    # Front/Back holes (2 cols x 3 rows) - punch through Z axis
    cols, rows = 2, 3
    for i in range(cols):
        for j in range(rows):
            x_start = int(n * (i + 0.25) / (cols + 0.5))
            x_end = int(n * (i + 0.75) / (cols + 0.5))
            y_start = int(n * (j + 0.25) / (rows + 0.5))
            y_end = int(n * (j + 0.75) / (rows + 0.5))
            cube[x_start:x_end, y_start:y_end, :] = False

    # Side holes (4 cols x 5 rows) - punch through X axis
    cols, rows = 4, 5
    for i in range(cols):
        for j in range(rows):
            z_start = int(n * (i + 0.25) / (cols + 0.5))
            z_end = int(n * (i + 0.75) / (cols + 0.5))
            y_start = int(n * (j + 0.25) / (rows + 0.5))
            y_end = int(n * (j + 0.75) / (rows + 0.5))
            cube[:, y_start:y_end, z_start:z_end] = False

    # Top holes (6 cols x 7 rows) - punch through Y axis
    cols, rows = 6, 7
    for i in range(cols):
        for j in range(rows):
            x_start = int(n * (i + 0.25) / (cols + 0.5))
            x_end = int(n * (i + 0.75) / (cols + 0.5))
            z_start = int(n * (j + 0.25) / (rows + 0.5))
            z_end = int(n * (j + 0.75) / (rows + 0.5))
            cube[x_start:x_end, :, z_start:z_end] = False

    return cube

def create_face_colors(cube):
    """Create colors based on face orientation."""
    n = cube.shape[0]
    colors = np.zeros(cube.shape + (4,), dtype=np.float32)

    # We'll color based on which face is visible
    for x in range(n):
        for y in range(n):
            for z in range(n):
                if cube[x, y, z]:
                    # Determine dominant face color based on position
                    # Blue for front (high z), Red for side (high x), Green for top (high y)

                    # Check neighbors to determine which faces are exposed
                    front_exposed = (z == n-1) or (z < n-1 and not cube[x, y, z+1])
                    right_exposed = (x == n-1) or (x < n-1 and not cube[x+1, y, z])
                    top_exposed = (y == n-1) or (y < n-1 and not cube[x, y+1, z])

                    # Base color - blend based on position for depth
                    r = 0.6 + 0.25 * (x / n)  # Red increases toward right
                    g = 0.6 + 0.25 * (y / n)  # Green increases toward top
                    b = 0.6 + 0.25 * (z / n)  # Blue increases toward front

                    colors[x, y, z] = [r, g, b, 1.0]

    return colors

def plot_custom_sponge():
    """Plot the custom sponge with colored faces."""
    fig = plt.figure(figsize=(12, 10), facecolor='white')
    ax = fig.add_subplot(111, projection='3d')

    print("Creating custom cube with hole patterns...")
    cube = create_custom_cube()

    print("Creating face colors...")
    colors = create_face_colors(cube)

    print("Rendering voxels...")
    ax.voxels(cube, facecolors=colors, edgecolor='#8888aa', linewidth=0.05)

    ax.set_title('Custom Sponge\nFront (blue): 2×3 holes | Side (red): 4×5 holes | Top (green): 6×7 holes',
                 fontsize=14, fontweight='bold', pad=15)

    ax.set_xticks([])
    ax.set_yticks([])
    ax.set_zticks([])
    ax.set_box_aspect([1, 1, 1])
    ax.view_init(elev=25, azim=45)

    # Add face labels
    ax.text(45, 21, 21, 'Red\n4×5', fontsize=10, color='darkred', ha='center')
    ax.text(21, 45, 21, 'Green\n6×7', fontsize=10, color='darkgreen', ha='center')
    ax.text(21, 21, 45, 'Blue\n2×3', fontsize=10, color='darkblue', ha='center')

    plt.tight_layout()

    output_path = '/home/tracy/development/Riemann/tuning/custom_sponge_faces.png'
    plt.savefig(output_path, dpi=200, bbox_inches='tight',
                facecolor='white', edgecolor='none')
    print(f"Saved to: {output_path}")
    plt.close()

if __name__ == "__main__":
    plot_custom_sponge()
