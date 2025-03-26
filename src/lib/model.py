class AssignmentModel:
    def __init__(self):
        self.model = [["0-morning", "1-morning", "2-morning"],
                      ["3-morning", "4-morning", "5-night"],
                      ["6-night", "7-night", "8-night"],
                      ["9-night", "10-night", "11-morning"], 
                      ["0-morning", "4-morning", "11-morning"],
                      ["1-morning", "3-morning", "7-night"],
                      ["5-night", "6-night", "10-night"],
                      ["8-night", "9-night", "2-morning"]]
        
        # NOTE: this model should satisfy
        # self.model = [["10-morning", "3-morning", "9-morning"],
        #               ["0-morning", "7-night", "5-morning"],
        #               ["8-night", "2-night", "11-night"],
        #               ["1-morning", "6-night", "4-night"], 
        #               ["1-morning", "3-morning", "5-morning"],
        #               ["2-night", "9-morning", "0-morning"],
        #               ["7-night", "4-night", "8-night"],
        #               ["11-night", "10-morning", "6-night"]]