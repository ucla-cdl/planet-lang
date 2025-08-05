import logging

class ColorFormatter(logging.Formatter):
    BRIGHT_PINK = "\033[95m"  # bright magenta (pink)
    WHITE = "\033[97m"
    RESET = "\033[0m"

    def format(self, record):
        # Format the original message first
        msg = super().format(record)

        # Replace the levelname (e.g., WARNING) with colored version
        # record.levelname is typically uppercase, e.g., 'WARNING'
        colored_levelname = f"{self.BRIGHT_PINK}{record.levelname}{self.RESET}"

        # Replace only the first occurrence of the levelname in the message
        # (usually appears at the start)
        msg = msg.replace(record.levelname, colored_levelname, 1)

        # Wrap the rest of the message in white color
        # (Assuming formatter outputs levelname followed by message)
        # Since we replaced levelname already, ensure msg ends with reset
        return f"{self.WHITE}{msg}{self.RESET}"


logger = logging.getLogger("planet")
if not logging.getLogger().hasHandlers():
    logging.basicConfig(level=logging.ERROR)
    logger.setLevel(logging.WARNING)
    handler = logging.StreamHandler()
    formatter = ColorFormatter('%(levelname)s: %(message)s')
    handler.setFormatter(formatter)
    logger.addHandler(handler)
    

logger.propagate = False

