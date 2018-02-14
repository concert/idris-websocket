module Main

import WebSocket

main : JS_IO ()
main = do
  ws <- websocket.new $ MkUrl "wss" "echo.websocket.org"
  -- consoleLog' ws
  websocket.onOpen ws $ \_ => do
    consoleLog "woot opened"
    websocket.onClose ws $ const $ consoleLog "aaand closed"
    websocket.onMessage ws $ \msg => do
      consoleLog $ "received" ++ msg
      websocket.close ws
      consoleLog "told to close"
    websocket.send ws "hello world!"
    consoleLog "sent hello world"
