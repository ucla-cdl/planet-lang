import pandas as pd
from .candl import *

class LatexExport:

    def __init__(self, design_data):
        """
        design_data: Could be a pandas DataFrame or
        any structure that can be converted into one.
        """
        self.df = design_data

    def to_latex(self):
        trials = [f"trial{i+1}" for i in range(len(self.df[0]))]
        df = pd.DataFrame(self.df, columns=trials)
        try:
            filepath = "../outputs/design.tex"
            create_directory_for_file(filepath)
            with open(filepath, 'w', encoding='utf-8') as tex_file:
                tex_file.write(df.to_latex())
            print(f"success")
        except Exception as e:
            print(f"An error occurred: {e}")