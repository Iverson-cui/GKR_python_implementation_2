import csv


class CSVGroupGenerator:
    """
    A class to generate CSV files with groups of type,number,number format or input,number format.
    Numbers increment continuously across all groups and lines.
    """

    def __init__(self, group_type="type", mode="gate"):
        """
        Initialize the generator with a specific type for all groups.

        Args:
            group_type (str): The type value that will be used for all groups
            mode (str): Either "gate" or "input" to determine the format
        """
        self.group_type = group_type
        self.current_number = 0  # This tracks our incrementing counter
        self.mode = mode

    def generate_line(self, num_groups, input_value=None):
        """
        Generate a single line with the specified number of groups.
        Each line starts counting from 0 for gate mode.

        Args:
            num_groups (int): Number of groups to include in this line
            input_value (int): The value to use for all groups in input mode

        Returns:
            list: A list of elements that form one CSV line
        """
        line_elements = []
        
        if self.mode == "gate":
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
                # Move our counter forward to the next group
                line_counter += 2
        
        elif self.mode == "input":
            # For input mode, we add: "input", input_value for each group
            value = input_value if input_value is not None else 0
            for group in range(num_groups):
                line_elements.extend(
                    [
                        "input",  # Fixed type for input mode
                        value,    # The same value for all groups
                    ]
                )

        return line_elements

    def generate_csv_file(self, filename, line_configurations, input_value=None):
        """
        Generate a complete CSV file based on line configurations.

        Args:
            filename (str): Name of the output CSV file
            line_configurations (list): List of integers, each specifying
                                      the number of groups for that line
            input_value (int): The value to use for all groups in input mode
        """
        with open(filename, "w", newline="") as csvfile:
            writer = csv.writer(csvfile)

            # Generate each line according to the configuration
            for line_num, num_groups in enumerate(line_configurations, 1):
                if self.mode == "input":
                    line_data = self.generate_line(num_groups, input_value)
                else:
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

    # Example 1: Gate mode (original behavior)
    print("Example 1: Creating a file with gate mode")
    generator1 = CSVGroupGenerator("sensor", "gate")

    # Create a file where each line has 3 groups
    line_config = [3, 3, 3]  # 3 lines, each with 3 groups
    generator1.generate_csv_file("example1_gate.csv", line_config)
    print()

    # Example 2: Input mode
    print("Example 2: Creating a file with input mode")
    generator2 = CSVGroupGenerator("data", "input")

    # Single line with 4 groups, all with value 42
    line_config = [4]  # 1 line with 4 groups
    generator2.generate_csv_file("example2_input.csv", line_config, input_value=42)
    print()


def interactive_csv_generator():
    """
    Interactive function to create a custom CSV file based on user input.

    The CSV format goes like this:
    - Gate mode: type,number1,number2. These 3 elements are combined into a group.
    - Input mode: input,number. These 2 elements are combined into a group.

    You can choose how many groups do you want in a line.
    In gate mode, numbers increase from 0 and increment by 1. Each line the number starts from 0.
    In input mode, you specify one value that applies to all groups in the single line.
    """
    print("\n=== Interactive CSV Generator ===")

    # Get the mode from user
    while True:
        mode = input("Choose mode - 'gate' or 'input' (default: 'gate'): ").strip().lower()
        if mode in ["gate", "input", ""]:
            if mode == "":
                mode = "gate"
            break
        else:
            print("Please enter 'gate' or 'input'")

    if mode == "gate":
        # Get the type from user
        group_type = input("Enter the type for all groups (default: 'type'): ").strip()
        if not group_type:
            group_type = "type"

        # Create generator with user's type
        generator = CSVGroupGenerator(group_type, mode)

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

        # Get number of groups per line (same for all lines)
        while True:
            try:
                groups_per_line = int(input("How many groups per line? "))
                if groups_per_line > 0:
                    break
                else:
                    print("Please enter a positive number.")
            except ValueError:
                print("Please enter a valid number.")

        # Create line configurations with the same number of groups for each line
        line_configurations = [groups_per_line] * num_lines

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

    elif mode == "input":
        # Create generator for input mode
        generator = CSVGroupGenerator("input", mode)

        # Get number of groups (only one line in input mode)
        while True:
            try:
                num_groups = int(input("How many groups in the line? "))
                if num_groups > 0:
                    break
                else:
                    print("Please enter a positive number.")
            except ValueError:
                print("Please enter a valid number.")

        # Get the value for all groups
        while True:
            try:
                input_value = int(input("Enter the value for all groups: "))
                break
            except ValueError:
                print("Please enter a valid integer.")

        # Single line configuration
        line_configurations = [num_groups]

        # Get filename
        filename = input("Enter filename (default: 'output.csv'): ").strip()
        if not filename:
            filename = "output.csv"
        if not filename.endswith(".csv"):
            filename += ".csv"

        # Generate the file
        print(f"\nGenerating {filename}...")
        generator.generate_csv_file(filename, line_configurations, input_value)
        print(f"File '{filename}' created successfully!")


if __name__ == "__main__":
    # Run the demonstration
    demonstrate_usage()

    # Run the interactive generator
    interactive_csv_generator()
