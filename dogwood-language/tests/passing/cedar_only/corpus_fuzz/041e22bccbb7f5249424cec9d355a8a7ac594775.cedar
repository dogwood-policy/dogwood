forbid(
  principal in a::"",
  action == Action::"",
  resource in a::""
) when {
  (true && (if (({":": [":"]}[":"]).containsAny({":": [ip("242.242.242.242"), ip("242.242.242.242")]}[":"])) then (({":": [":", ":"]}[":"]).containsAny({":": [":", ":"]}[":"])) else (({":": [":", ":"]}[":"]).containsAny({":": [":", ":"]}[":"])))) && (((if false then {":": [":", ":"]} else {":": [":"]})[":"]).containsAny([ip("0.169.169.102"), ip("0.0.0.0")]))
};
