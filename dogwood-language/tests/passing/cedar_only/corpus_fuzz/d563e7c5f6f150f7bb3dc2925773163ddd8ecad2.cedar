@A000000000("")
forbid(
  principal is a in a::"",
  action in [Action::"action",Action::"action",Action::"action"],
  resource is a in a::""
) when {
  ((true && ((if ("" like "") then (if true then {"": {"": {"": {}}}} else {"": {"": {"": {}}}}) else (if false then context else {"": {"": {"": {}}}})) == (if ("" like "") then (if true then {"": {"": {"": {}}}} else context) else {"": context}))) && ((if (!true) then (if true then {"": {"": {"": {}}}} else {"": {"": {"": {}}}}) else (if true then {"": {"": {"": {}}}} else {"": {"": {"": {}}}})) == (({"": {"": {"": {"": {"": {}}}}}}[""])[""]))) && ((if ({"": false}[""]) then ({"|": {"": true}}["|"]) else {"": true})[""])
};
