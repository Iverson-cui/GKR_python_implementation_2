import csv


class CSVGroupGenerator:
    """
    A class to generate CSV files with groups of type,number,number,... format or input,number format.
    Numbers increment continuously across all groups and lines, with wrapping at max_value.
    """

    def __init__(
        self, group_type="type", mode="gate", numbers_per_group=2, max_value=None
    ):
        """
        Initialize the generator with a specific type for all groups.

        Args:
            group_type (str): The type value that will be used for all groups
            mode (str): Either "gate" or "input" to determine the format
            numbers_per_group (int): Number of integers in each group (default: 2)
            max_value (int): Maximum value for integers before wrapping to 0 (default: None, no wrapping)
        """
        self.group_type = group_type
        self.current_number = 0  # This tracks our incrementing counter
        self.mode = mode
        self.numbers_per_group = numbers_per_group
        self.max_value = max_value

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

            # For each group, we add: type, followed by numbers_per_group integers
            for _ in range(num_groups):
                # Start with the group type
                group_data = [self.group_type]

                # Add the specified number of integers
                for _ in range(self.numbers_per_group):
                    # Apply wrapping if max_value is set
                    if self.max_value is not None:
                        current_value = line_counter % (self.max_value + 1)
                    else:
                        current_value = line_counter

                    group_data.append(current_value)
                    line_counter += 1

                line_elements.extend(group_data)

        elif self.mode == "input":
            # For input mode, we add: "input", input_value for each group
            value = input_value if input_value is not None else 0
            for _ in range(num_groups):
                line_elements.extend(
                    [
                        "input",  # Fixed type for input mode
                        value,  # The same value for all groups
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
        with open(filename, "w", newline="", encoding="utf-8") as csvfile:
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

    def generate_line_with_config(self, config):
        """
        Generate a single line with a specific configuration.

        Args:
            config (dict): Configuration for this line containing:
                - num_groups (int): Number of groups in this line
                - group_type (str): Type for all groups in this line
                - numbers_per_group (int): Number of integers per group (ignored if group_type is 'input')
                - max_value (int or None): Maximum value before wrapping
                - input_value (int, optional): For input mode only
                - duplicate_mode (bool, optional): If True, duplicate each group

        Returns:
            list: A list of elements that form one CSV line
        """
        line_elements = []
        line_counter = 0  # Start each line from 0
        duplicate_mode = config.get("duplicate_mode", False)

        # Calculate effective number of groups (considering duplicates)
        effective_groups = (
            config["num_groups"] // 2 if duplicate_mode else config["num_groups"]
        )

        # For each unique group, we add: type, followed by integers
        for _ in range(effective_groups):
            # Start with the group type
            group_data = [config["group_type"]]

            # Determine how many integers to add based on group type
            if config["group_type"] == "input":
                # Input groups have only 1 integer and use incrementing counter
                integers_in_group = 1
                # Apply wrapping if max_value is set
                if config["max_value"] is not None:
                    current_value = line_counter % (config["max_value"] + 1)
                else:
                    current_value = line_counter
                group_data.append(current_value)
                line_counter += 1
            else:
                # Other groups use the specified numbers_per_group
                integers_in_group = config["numbers_per_group"]

                # Add the specified number of integers
                for _ in range(integers_in_group):
                    # Apply wrapping if max_value is set
                    if config["max_value"] is not None:
                        current_value = line_counter % (config["max_value"] + 1)
                    else:
                        current_value = line_counter

                    group_data.append(current_value)
                    line_counter += 1

            # Add the group to line_elements
            if duplicate_mode:
                # Add the group twice
                line_elements.extend(group_data)
                line_elements.extend(group_data)
            else:
                # Add the group once
                line_elements.extend(group_data)

        return line_elements

    def generate_csv_file_with_configs(self, filename, line_configs):
        """
        Generate a complete CSV file with individual line configurations.

        Args:
            filename (str): Name of the output CSV file
            line_configs (list): List of configuration dictionaries, each specifying
                               the configuration for that line
        """
        with open(filename, "w", newline="", encoding="utf-8") as csvfile:
            writer = csv.writer(csvfile)

            # Generate each line according to its configuration
            for line_num, config in enumerate(line_configs, 1):
                line_data = self.generate_line_with_config(config)

                writer.writerow(line_data)
                # Determine display info based on group type
                duplicate_info = (
                    " (DUPLICATE MODE)" if config.get("duplicate_mode", False) else ""
                )
                if config["group_type"] == "input":
                    display_info = (
                        f"Line {line_num}: {config['num_groups']} groups (type: {config['group_type']}, "
                        f"ints/group: 1, max: {config['max_value']}){duplicate_info} -> "
                        f"{','.join(map(str, line_data))}"
                    )
                else:
                    display_info = (
                        f"Line {line_num}: {config['num_groups']} groups (type: {config['group_type']}, "
                        f"ints/group: {config['numbers_per_group']}, max: {config['max_value']}){duplicate_info} -> "
                        f"{','.join(map(str, line_data))}"
                    )

                print(display_info)

    def reset_counter(self):
        """Reset the number counter back to 0."""
        self.current_number = 0


def demonstrate_usage():
    """
    Demonstrate different ways to use the CSV generator.
    """
    print("=== CSV Group Generator Demo ===\n")

    # Example 1: Gate mode with default 2 numbers per group
    print("Example 1: Creating a file with gate mode (2 numbers per group)")
    generator1 = CSVGroupGenerator("sensor", "gate")

    # Create a file where each line has 3 groups
    line_config = [3, 3, 3]  # 3 lines, each with 3 groups
    generator1.generate_csv_file("example1_gate.csv", line_config)
    print()

    # Example 2: Gate mode with 4 numbers per group and max value of 5
    print(
        "Example 2: Creating a file with gate mode (4 numbers per group, max value 5)"
    )
    generator2 = CSVGroupGenerator("data", "gate", numbers_per_group=4, max_value=5)

    # Create a file where each line has 2 groups
    line_config = [2, 2]  # 2 lines, each with 2 groups
    generator2.generate_csv_file("example2_gate.csv", line_config)
    print()

    # Example 3: Input mode
    print("Example 3: Creating a file with input mode")
    generator3 = CSVGroupGenerator("data", "input")

    # Single line with 4 groups, all with value 42
    line_config = [4]  # 1 line with 4 groups
    generator3.generate_csv_file("example3_input.csv", line_config, input_value=42)
    print()

    # Example 4: Advanced - Different configurations per line including input type
    print(
        "Example 4: Creating a file with different configurations per line (including input type)"
    )
    generator4 = CSVGroupGenerator(mode="gate")

    # Define different configurations for each line
    advanced_configs = [
        {"num_groups": 2, "group_type": "add", "numbers_per_group": 3, "max_value": 7},
        {
            "num_groups": 4,
            "group_type": "mul",
            "numbers_per_group": 2,
            "max_value": None,
        },
        {
            "num_groups": 3,
            "group_type": "input",
            "numbers_per_group": 1,
            "max_value": 5,
        },
        {"num_groups": 1, "group_type": "sub", "numbers_per_group": 4, "max_value": 3},
    ]

    generator4.generate_csv_file_with_configs("example4_advanced.csv", advanced_configs)
    print()


def interactive_csv_generator():
    """
    Interactive function to create a custom CSV file based on user input.

    The CSV format goes like this:
    - Gate mode: type,number1,number2,... with customizable number of integers in a group.
    - Input mode: input,number. These 2 elements are combined into a group.

    You can choose how many groups do you want in a line.
    In gate mode, numbers increase from 0 and increment by 1. Each line the number starts from 0.
    Numbers can wrap around at a specified maximum value.
    In input mode, you specify one value that applies to all groups in the single line.
    Duplicate mode: Each group appears twice consecutively in the line.
    """
    print("\n=== Interactive CSV Generator ===")

    # Get the mode from user
    while True:
        mode = (
            input("Choose mode - 'gate' or 'input' (default: 'gate'): ").strip().lower()
        )
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

        # Get number of integers per group
        while True:
            try:
                numbers_per_group = int(
                    input("How many integers per group (default: 2)? ")
                )
                if numbers_per_group > 0:
                    break
                else:
                    print("Please enter a positive number.")
            except ValueError:
                numbers_per_group = 2
                break

        # Get maximum value for wrapping
        while True:
            max_value_input = input(
                "Enter maximum value for integers (press Enter for no limit): "
            ).strip()
            if max_value_input == "":
                max_value = None
                break
            try:
                max_value = int(max_value_input)
                if max_value >= 0:
                    break
                else:
                    print("Please enter a non-negative number.")
            except ValueError:
                print("Please enter a valid number or press Enter for no limit.")

        # Create generator with user's parameters
        generator = CSVGroupGenerator(group_type, mode, numbers_per_group, max_value)

        # Ask about duplicate mode
        while True:
            duplicate_input = (
                input(
                    "Enable duplicate mode? Each group will appear twice (y/n, default: n): "
                )
                .strip()
                .lower()
            )
            if duplicate_input in ["y", "yes", "n", "no", ""]:
                duplicate_mode = duplicate_input in ["y", "yes"]
                break
            else:
                print("Please enter 'y' for yes or 'n' for no.")

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

        # Create line configurations with the same configuration for each line
        line_configs = []
        for _ in range(num_lines):
            config = {
                "num_groups": groups_per_line,
                "group_type": group_type,
                "numbers_per_group": numbers_per_group,
                "max_value": max_value,
                "duplicate_mode": duplicate_mode,
            }
            line_configs.append(config)

        # Get filename
        filename = input("Enter filename (default: 'output.csv'): ").strip()
        if not filename:
            filename = "output.csv"
        if not filename.endswith(".csv"):
            filename += ".csv"

        # Generate the file using the advanced method
        generator_advanced = CSVGroupGenerator(mode=mode)
        print(f"\nGenerating {filename}...")
        generator_advanced.generate_csv_file_with_configs(filename, line_configs)
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


def advanced_interactive_csv_generator():
    """
    Advanced interactive function to create a custom CSV file with individual line configurations.

    Allows you to specify different configurations for each line:
    - Group type for each line (can mix different types like 'add', 'mul', 'input', etc.)
    - Number of groups per line
    - Numbers per group (ignored for 'input' type groups which always have 1)
    - Maximum value for wrapping
    - Duplicate mode (duplicates each group in the line)

    The increment logic applies to all group types including 'input':
    - Numbers start from 0 for each line
    - Numbers increment by 1 within each line
    - If max_value is set, numbers wrap around (e.g., max_value=5 means 0,1,2,3,4,5,0,1,...)
    - If duplicate mode is enabled, each group appears twice consecutively
    - 'input' type groups now also use incrementing numbers instead of fixed values
    """
    print("\n=== Advanced Interactive CSV Generator ===")
    print("Configure each line individually with different parameters.")

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

    # Collect configuration for each line
    line_configs = []

    for line_num in range(1, num_lines + 1):
        print(f"\n--- Configuring Line {line_num} ---")

        # Get group type for this line
        group_type = input(
            f"Enter group type for line {line_num} (default: 'type'): "
        ).strip()
        if not group_type:
            group_type = "type"

        # Get number of groups for this line
        while True:
            try:
                num_groups = int(input(f"Number of groups in line {line_num}: "))
                if num_groups > 0:
                    break
                else:
                    print("Please enter a positive number.")
            except ValueError:
                print("Please enter a valid number.")

        # Get number of integers per group for this line (only if not input type)
        if group_type.lower() == "input":
            numbers_per_group = 1  # Input groups always have 1 integer
            print("Note: 'input' groups automatically have 1 integer per group")
        else:
            while True:
                try:
                    numbers_per_group = int(
                        input(
                            f"How many integers per group in line {line_num} (default: 2)? "
                        )
                    )
                    if numbers_per_group > 0:
                        break
                    else:
                        print("Please enter a positive number.")
                except ValueError:
                    numbers_per_group = 2
                    break

        # Get maximum value for this line
        while True:
            max_value_input = input(
                f"Max value for integers in line {line_num} (press Enter for no limit): "
            ).strip()
            if max_value_input == "":
                max_value = None
                break
            try:
                max_value = int(max_value_input)
                if max_value >= 0:
                    break
                else:
                    print("Please enter a non-negative number.")
            except ValueError:
                print("Please enter a valid number or press Enter for no limit.")

        # Ask about duplicate mode
        while True:
            duplicate_input = (
                input(
                    f"Enable duplicate mode for line {line_num}? Each group will appear twice (y/n, default: n): "
                )
                .strip()
                .lower()
            )
            if duplicate_input in ["y", "yes", "n", "no", ""]:
                duplicate_mode = duplicate_input in ["y", "yes"]
                break
            else:
                print("Please enter 'y' for yes or 'n' for no.")

        # Handle input type configuration
        if group_type.lower() == "input":
            config = {
                "num_groups": num_groups,
                "group_type": "input",
                "numbers_per_group": 1,
                "max_value": max_value,
                "duplicate_mode": duplicate_mode,
            }
        else:
            config = {
                "num_groups": num_groups,
                "group_type": group_type,
                "numbers_per_group": numbers_per_group,
                "max_value": max_value,
                "duplicate_mode": duplicate_mode,
            }

        line_configs.append(config)
        print(f"Line {line_num} configured: {config}")

    # Get filename
    filename = input("\nEnter filename (default: 'output.csv'): ").strip()
    if not filename:
        filename = "output.csv"
    if not filename.endswith(".csv"):
        filename += ".csv"

    # Create generator and generate the file
    generator = CSVGroupGenerator(
        mode="gate"
    )  # Default mode, actual behavior determined by line configs
    print(f"\nGenerating {filename}...")
    generator.generate_csv_file_with_configs(filename, line_configs)
    print(f"File '{filename}' created successfully!")


if __name__ == "__main__":
    print("=== CSV Generator Suite ===")
    print("Choose your preferred generator:")
    print("1. Demo - See examples of different configurations")
    print("2. Basic Interactive - Same configuration for all lines")
    print("3. Advanced Interactive - Different configuration per line")

    while True:
        choice = input("\nEnter your choice (1-3): ").strip()

        if choice == "1":
            demonstrate_usage()
            break
        elif choice == "2":
            interactive_csv_generator()
            break
        elif choice == "3":
            advanced_interactive_csv_generator()
            break
        else:
            print("Please enter 1, 2, or 3.")
