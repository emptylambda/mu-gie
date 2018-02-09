count :: String -> Int
count s = length [ a | [a] <- lines s, length a > 10]
