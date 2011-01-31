{-# LANGUAGE ForeignFunctionInterface #-}

module Database.DSH.Pathfinder
    (
      compileFerry
    , compileFerryOpt
    , OutputFormat (..)
    , XmlString
    , ErrorString
    , OutputString
    , OptArgs
    ) where

import Foreign
import Foreign.C

import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import qualified Data.ByteString as B

#include <pf_ferry.h>

--------------------------------------------------------------------------------
-- Enum: OutputFormat

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


--------------------------------------------------------------------------------
-- FFI functions

type XmlString    = String
type ErrorString  = String
type OutputString = String
type OptArgs = String


foreign import ccall safe "PFcompile_ferry"
    c'PFcompile_ferry :: Ptr CString -> CString -> CString -> CInt -> IO CInt

-- | Accept a logical query plan bundle in XML format and transform it into one
-- of the output formats.
compileFerry :: XmlString                   -- ^ Input XML plan
             -> OutputFormat
             -> IO (Either ErrorString OutputString)
compileFerry xml output = do
    B.useAsCString (T.encodeUtf8 (T.pack xml)) $ \c'xml ->
      alloca $ \ptr -> alloca $ \c'err -> do

          -- run PFcompile_ferry
          ci <- c'PFcompile_ferry ptr c'err c'xml (outputFormatToCInt output)

          if ci == 0
             then Right `fmap` (peek ptr >>= B.packCString >>= (return . T.unpack . T.decodeUtf8))
             else Left  `fmap` (B.packCString c'err >>= (return . T.unpack . T.decodeUtf8))


foreign import ccall safe "PFcompile_ferry_opt"
    c'PFcompile_ferry_opt :: Ptr CString -> CString -> CString -> CInt -> CString -> IO CInt

-- | Accept a logical query plan bundle in XML format, optimize it based on the
-- argument 'OptArgs' or (if 'Nothing') the default optimization arguments in
-- @PFopt_args@, and transform it into one of the output formats.
compileFerryOpt :: XmlString
                -> OutputFormat
                -> Maybe OptArgs                        -- ^ Optimization arguments (see pf option -o)
                -> IO (Either ErrorString OutputString)
compileFerryOpt xml output optimization = do
    B.useAsCString (T.encodeUtf8 (T.pack xml)) $ \c'xml ->
      alloca $ \ptr -> alloca $ \c'err -> do

          -- Read optimization arguments, use nullPtr if nothing is given
          opt <- maybe (return nullPtr)
                       newCString
                       optimization

          -- run PFcompile_ferry_opt
          ci <- c'PFcompile_ferry_opt ptr c'err c'xml (outputFormatToCInt output) opt
          if ci == 0
             then Right `fmap` (peek ptr >>= B.packCString >>= (return . T.unpack . T.decodeUtf8))
             else Left  `fmap` (B.packCString c'err >>= (return . T.unpack . T.decodeUtf8))
