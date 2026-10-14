# 0086_enum_app_enum_in_record_argument

App-owned enum fields are passed inside a `record` argument (the whole `context.input`).

Like `0074`, each enum field reaches the script as its bare id (`"high"`): the record is walked by its declared type. As uid text (`Drupe::AlertLevel::"high"`) the comparisons would always be false, and the high and abuse alerts would be allowed.
