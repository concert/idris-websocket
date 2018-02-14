IDRIS=idris

build:
	$(IDRIS) --build idris-websocket.ipkg

install:
	$(IDRIS) --install idris-websocket.ipkg

.PHONY: test  # Because the directory 'test' exists.
test: install
	$(IDRIS) --codegen javascript -p idris-websocket -o test/main.js test/Main.idr

clean:
	$(IDRIS) --clean idris-websocket.ipkg
	$(RM) test/main.js
