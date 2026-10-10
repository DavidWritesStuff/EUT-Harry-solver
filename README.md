# EUT Harry's Solver

A Python GUI application that helps solve Harry's puzzle in **Everything Upgrade Tree (EUT)** by automatically evaluating and ranking entries in a 5×5 grid.

Built with Python and Tkinter, the application combines multiple input formats, real-time evaluation, a ranked results table, and an optional HUD overlay.

## Features

- **Automatic evaluation** — entries are evaluated as you edit the grid.
- **5×5 input grid** — enter up to 25 puzzle entries.
- **Four input formats (P1–P4)** — supports ordinary numbers, shifted-symbol numbers, numbers in different bases, and mathematical expressions.
- **Linear equation solving** — solve supported linear equations for `x`.
- **Variable assignments** — evaluate sequential assignments using variables such as `a`, `b`, `c`, and `x`.
- **Automatic ranking** — valid entries are sorted in ascending order by their calculated values.
- **Error handling** — invalid entries are identified, with error details available in the output and log.
- **Live results** — see updated results as you edit the grid.
- **Light and dark themes** — choose a theme and customize the background color using RGB sliders.
- **HUD overlay** — display cell rankings in a separate, always-on-top 5×5 grid, with adjustable opacity.
- **Action and error log** — inspect application activity, successful operations, and errors.
- **Settings persistence** — save window positions, theme preferences, background color, and optionally grid contents.
- **Compact interface** — use a more compact layout with a quick menu.
- **Keyboard navigation** — move between grid cells using Enter and Shift+Enter.
- **Clipboard export** — copy the complete 25-row results table.

## Requirements

- Python 3.9 or newer
- Tkinter, usually included with standard Python installations
- Windows for the HUD overlay's click-through functionality

The application uses Python's standard library and does not require third-party packages.

## Getting Started

### 1. Download the repository

Clone the repository using Git:

```bash
git clone https://github.com/DavidWritesStuff/EUT-Harry-solver.git
cd EUT-Harry-solver
```

Alternatively, download the repository as a ZIP file from GitHub and extract it.

### 2. Run the application

Run the following command from the project directory:

```bash
python EUT-Harry-solver.py
```

On Windows, you can also use:

```bash
py EUT-Harry-solver.py
```

The graphical interface will open automatically.

## Supported Input Formats

The application automatically detects the input format of each non-empty cell.

| Format | Description | Example |
|---|---|---|
| P1 | Ordinary numbers | `42`, `-7`, `3.14` |
| P2 | Shifted-symbol numbers | `!@` → `12` |
| P3 | Numbers in bases 2–36 | `101(2)` → `5` |
| P3 | Alternative base notation | `1A(16)` → `26` |
| P4 | Mathematical expressions | `2^8`, `10 mod 3` |
| P4 | Linear equations | `2x + 5 = 11` → `x = 3` |
| P4 | Variable assignments | `a=5, x=a^2` → `x = 25` |

### Mathematical expressions

Supported operators include:

- Addition, subtraction, multiplication, and division
- Floor division and modulo
- Exponentiation using `^` or `**`
- Factorials using `!`
- Implicit multiplication in supported forms

Available mathematical functions include `sqrt`, `sin`, `cos`, `tan`, `log`, `log10`, `floor`, `ceil`, `round`, `abs`, `min`, `max`, and `sum`, alongside constants such as `pi`, `e`, and `tau`.

The application uses restricted AST-based evaluation rather than unrestricted Python `eval()`.

**Note:** Linear equations must be linear in `x`. Assignment chains are evaluated sequentially and must define `x`.

## How Ranking Works

1. Enter values or expressions into the 5×5 grid.
2. The application automatically evaluates each cell.
3. Valid entries are sorted in ascending order by their calculated numeric values.
4. Equal values retain their original grid order.
5. Invalid and empty cells are placed after valid entries.

The output contains exactly 25 rows and uses three states:

- `OK` — the entry was evaluated successfully.
- `ERR` — the entry could not be evaluated.
- `EMPTY` — the cell contains no input.

Each row also includes identifying information such as the cell index, rank, detected input format, calculated value, and grid coordinates.

## HUD Overlay

The optional HUD overlay displays the ranking of each cell in a separate 5×5 grid.

It includes:

- An always-on-top overlay window
- Adjustable opacity
- A control window for locking and unlocking the overlay
- Click-through functionality on Windows

The overlay displays calculated rankings; it does not automatically detect or read puzzle entries from the game screen. You must enter the puzzle data into the application yourself.

## Settings and Configuration

The application saves its configuration in the following file in your home directory:

```text
.eut_harry_gui.json
```

Depending on your settings, this file can store the selected theme, background color, window positions, and grid contents.

Grid contents are saved only when the corresponding option is enabled.

## Project Structure

```text
EUT-Harry-solver/
└── EUT-Harry-solver.py
```

The main Python file contains the input parsers, mathematical evaluation engine, ranking logic, Tkinter interface, settings management, logging system, and HUD overlay.

## Technologies

- **Python** — application logic and calculations
- **Tkinter / ttk** — graphical user interface
- **AST** — restricted mathematical expression evaluation
- **JSON** — configuration persistence
- **ctypes** — Windows-specific overlay functionality

## Limitations

- Puzzle entries must be entered manually.
- Only supported input formats and mathematical operations can be evaluated.
- HUD click-through functionality is Windows-specific.
- The application does not automatically interact with or read data from the game itself.

## Contributing

Suggestions, bug reports, and improvements are welcome. Feel free to explore the source code, report issues, or propose improvements.

## Author

Created by [DavidWritesStuff](https://github.com/DavidWritesStuff).

## Disclaimer

This is an independent community project and is not an official tool or product of Everything Upgrade Tree or Roblox.
