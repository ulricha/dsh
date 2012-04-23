{-# LANGUAGE ForeignFunctionInterface #-}

module Database.Pathfinder
    (
      pathfinder
    , OutputFormat (..)
    , XmlString
    , ErrorString
    , OutputString
    , OptString
    ) where

import Foreign
import Foreign.C

import Control.Concurrent.MVar (MVar,takeMVar,putMVar,newEmptyMVar)
import qualified System.IO.Unsafe

import qualified Data.Text as T
import Data.Text.Encoding.Error
import qualified Data.Text.Encoding as T
import qualified Data.ByteString as B

-- | This is a global synchronisation variable used to guard calls to the
-- Pathfinder C library. The C library appears not to be thread safe and this
-- variable is used to make sure that only one pathfinder call is made at time
-- even in the presence of parallel or concurrent program execution.
{-# NOINLINE globalMVar #-}
globalMVar :: MVar ()
globalMVar = System.IO.Unsafe.unsafePerformIO (newEmptyMVar)


#include <pathfinder.h>

newtype COutputFormat = COutputFormat { unCOutputFormat :: CInt }
#{enum COutputFormat, COutputFormat
    , c_PFoutput_format_sql = PFoutput_format_sql
    , c_PFoutput_format_xml = PFoutput_format_xml
    , c_PFoutput_format_dot = PFoutput_format_dot
}

data OutputFormat
    = OutputSql
    | OutputXml
    | OutputDot

outputFormatToCInt :: OutputFormat -> CInt
outputFormatToCInt output = unCOutputFormat $
    case output of
         OutputSql -> c_PFoutput_format_sql
         OutputXml -> c_PFoutput_format_xml
         OutputDot -> c_PFoutput_format_dot


type XmlString    = String
type ErrorString  = String
type OutputString = String
type OptString    = String


foreign import ccall safe "PFcompile_ferry_opt"
    c_PFcompile_ferry_opt :: Ptr CString -> CString -> CString -> CInt -> CString -> IO CInt

-- | Relational optimiser and code generator
pathfinder :: XmlString     -- ^ A table algebra plan bundle in XML format
           -> OptString     -- ^ An optimisation string (empty string indicates default optimisations)
           -> OutputFormat  -- ^ Output format
           -> IO (Either ErrorString OutputString)
pathfinder xml optimisation output = do
  putMVar  globalMVar ()
  let bs = T.encodeUtf8 (T.pack xml)
  r <- B.useAsCString bs $ \c_xml -> 
          alloca            $ \c_ptr ->
            alloca            $ \c_err -> do
              c_opt <-  case optimisation of
                          [] -> return nullPtr
                          _  -> newCString optimisation

              ci <- c_PFcompile_ferry_opt c_ptr c_err c_xml (outputFormatToCInt output) c_opt
              free c_opt

              if ci == 0
                 then do
                   c_string <- peek c_ptr
                   r <- fmap (T.unpack . T.decodeUtf8With lenientDecode) (B.packCString c_string)
                   free c_string
                   return (Right r)
                 else fmap (Left . T.unpack .  T.decodeUtf8With lenientDecode)  (B.packCString c_err)
  takeMVar globalMVar
  return r