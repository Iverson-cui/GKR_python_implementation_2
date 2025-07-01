import csv


class CSVGroupGenerator:
    """
    A class to generate CSV files with groups of type,number,number format.
    Numbers increment continuously across all groups and lines.
    """

    def __init__(self, group_type="type"):
        """
        Initialize the generator with a specific type for all groups.

        Args:
            group_type (str): The type value that will be used for all groups
        """
        self.group_type = group_type
        self.current_number = 0  # This tracks our incrementing counter

    def generate_line(self, num_groups):
        """
        Generate a single line with the specified number of groups.
        Each line starts counting from 0.

        Args:
            num_groups (int): Number of groups to include in this line

        Returns:
            list: A list of elements that form one CSV line
        """
        line_elements = []
        line_counter = 0  # Start each line from 0

        # For each group, we add: type, line_counter, line_counter+1
        for group in range(num_groups):
            line_elements.extend(
                [
                    self.group_type,  # The type (same for all groups)
                    line_counter,  # First incrementing number (starts at 0 each line)
                    line_counter + 1,  # Second incrementing number
                ]
            )
            # Move our counter forward by 2 for the next group
            line_counter += 2

        return line_elements

    def generate_csv_file(self, filename, line_configurations):
        """
        Generate a complete CSV file based on line configurations.

        Args:
            filename (str): Name of the output CSV file
            line_configurations (list): List of integers, each specifying
                                      the number of groups for that line
        """
        with open(filename, "w", newline="") as csvfile:
            writer = csv.writer(csvfile)

            # Generate each line according to the configuration
            for line_num, num_groups in enumerate(line_configurations, 1):
                line_data = self.generate_line(num_groups)
                writer.writerow(line_data)
                print(
                    f"Line {line_num}: {num_groups} groups -> {','.join(map(str, line_data))}"
                )

    def reset_counter(self):
        """Reset the number counter back to 0."""
        self.current_number = 0


def demonstrate_usage():
    """
    Demonstrate different ways to use the CSV generator.
    """
    print("=== CSV Group Generator Demo ===\n")

    # Example 1: Simple usage with consistent groups per line
    print("Example 1: Creating a file with consistent group sizes")
    generator1 = CSVGroupGenerator("sensor")

    # Create a file where each line has 3 groups
    line_config = [3, 3, 3]  # 3 lines, each with 3 groups
    generator1.generate_csv_file("example1.csv", line_config)
    print()

    # Example 2: Variable number of groups per line
    print("Example 2: Creating a file with variable group sizes")
    generator2 = CSVGroupGenerator("data")

    # Different number of groups per line
    line_config = [2, 4, 1, 3]  # 4 lines with varying group counts
    generator2.generate_csv_file("example2.csv", line_config)
    print()

    # Example 3: Interactive mode
    print("Example 3: Interactive configuration")
    generator3 = CSVGroupGenerator("item")

    # Simulate user input (in real use, you'd get this from input())
    simulated_user_choices = [
        ("How many lines? ", "2"),
        ("Groups in line 1? ", "3"),
        ("Groups in line 2? ", "2"),
    ]

    print("Simulating interactive input:")
    for prompt, response in simulated_user_choices:
        print(f"{prompt}{response}")

    line_config = [3, 2]  # Based on simulated input
    generator3.generate_csv_file("example3.csv", line_config)


def interactive_csv_generator():
    """
    Interactive function to create a custom CSV file based on user input.

    The CSV format goes like this: type,number1,number2. These 3 elements are combined into a group. You can choose how many groups do you want in a line.
    In every line, type is the same in a line, number increase from 0 and increment by 1. Each line the number starts from 0.

    After running this file, you can select how many lines you want to generate, what is your type, how many gates do you want.
    """
    print("\n=== Interactive CSV Generator ===")

    # Get the type from user
    group_type = input("Enter the type for all groups (default: 'type'): ").strip()
    if not group_type:
        group_type = "type"

    # Create generator with user's type
    generator = CSVGroupGenerator(group_type)

    # Get number of lines
    while True:
        try:
            num_lines = int(input("How many lines do you want in the CSV? "))
            if num_lines > 0:
                break
            else:
                print("Please enter a positive number.")
        except ValueError:
            print("Please enter a valid number.")

    # Get configuration for each line
    line_configurations = []
    for line_num in range(1, num_lines + 1):
        while True:
            try:
                groups = int(input(f"How many groups in line {line_num}? "))
                if groups > 0:
                    line_configurations.append(groups)
                    break
                else:
                    print("Please enter a positive number.")
            except ValueError:
                print("Please enter a valid number.")

    # Get filename
    filename = input("Enter filename (default: 'output.csv'): ").strip()
    if not filename:
        filename = "output.csv"
    if not filename.endswith(".csv"):
        filename += ".csv"

    # Generate the file
    print(f"\nGenerating {filename}...")
    generator.generate_csv_file(filename, line_configurations)
    print(f"File '{filename}' created successfully!")


if __name__ == "__main__":
    # Run the demonstration
    demonstrate_usage()

    # Uncomment the line below to run the interactive generator
    interactive_csv_generator()
