#ifndef IOKERNEL__LSTRING_META_CLASS_H
#define IOKERNEL__LSTRING_META_CLASS_H

#include "meta_class.h"
#include "iokernel_forwarders.h"


class LStringMetaClass : public MetaClass {
  friend class ObjectFactory;
public:
  virtual void write( const ObjectWrapper &obj,
		      OutputStream* outputStream ) const;

  virtual void read ( const ObjectWrapper &obj, 
		      InputStream* inputStream ) const;

  virtual void destruct( const ObjectWrapper &obj,
			 bool called_from_destructor ) const;

  Walker::ApplyStatus walk(const Address address,Walker &walk) const;

  static const LString &get_class_name();

protected:
  LStringMetaClass( LString metaClassName = emptyLString );

  static void constructor_function( Address place );
};


#endif










