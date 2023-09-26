Run a single step
  $ quint-ml-demo -seed 0 -steps 1
  Seed: 0
  =========
  board:
  
  -----
   | | 
  -----
   | | 
  -----
   | | 
  -----
  
  next player: X
  
  =========
  board:
  
  -----
  X| | 
  -----
   | | 
  -----
   | | 
  -----
  
  next player: O
  


Run the defalut 10 steps
  $ quint-ml-demo -seed 0
  Seed: 0
  =========
  board:
  
  -----
   | | 
  -----
   | | 
  -----
   | | 
  -----
  
  next player: X
  
  =========
  board:
  
  -----
  X| | 
  -----
   | | 
  -----
   | | 
  -----
  
  next player: O
  
  =========
  board:
  
  -----
  X|O| 
  -----
   | | 
  -----
   | | 
  -----
  
  next player: X
  
  =========
  board:
  
  -----
  X|O| 
  -----
  X| | 
  -----
   | | 
  -----
  
  next player: O
  
  =========
  board:
  
  -----
  X|O| 
  -----
  X| | 
  -----
   |O| 
  -----
  
  next player: X
  
  =========
  board:
  
  -----
  X|O| 
  -----
  X|X| 
  -----
   |O| 
  -----
  
  next player: O
  
  =========
  board:
  
  -----
  X|O|O
  -----
  X|X| 
  -----
   |O| 
  -----
  
  next player: X
  
  =========
  board:
  
  -----
  X|O|O
  -----
  X|X|X
  -----
   |O| 
  -----
  
  next player: O
  

Run with a different seed
  $ quint-ml-demo -seed 99 -steps 5
  Seed: 99
  =========
  board:
  
  -----
   | | 
  -----
   | | 
  -----
   | | 
  -----
  
  next player: X
  
  =========
  board:
  
  -----
  X| | 
  -----
   | | 
  -----
   | | 
  -----
  
  next player: O
  
  =========
  board:
  
  -----
  X|O| 
  -----
   | | 
  -----
   | | 
  -----
  
  next player: X
  
  =========
  board:
  
  -----
  X|O| 
  -----
   | | 
  -----
   | |X
  -----
  
  next player: O
  
  =========
  board:
  
  -----
  X|O|O
  -----
   | | 
  -----
   | |X
  -----
  
  next player: X
  
  =========
  board:
  
  -----
  X|O|O
  -----
   | | 
  -----
  X| |X
  -----
  
  next player: O
  
